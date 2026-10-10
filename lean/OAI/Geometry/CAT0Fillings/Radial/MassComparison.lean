import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.ExactMass
import OAI.Geometry.CAT0Fillings.Charts.LinearMass
import OAI.Geometry.CAT0Fillings.Currents.Pushforward
import OAI.Geometry.CAT0Fillings.Radial.Integrability

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open MeasureTheory Set Filter Metric Matrix CurrentOperations
open scoped Topology NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
theorem mass_eq_integral_majorant (hC : IsMetricCurrent C.action) {J : Euc k → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * J z)
      (volume.restrict C.domain))
    (hJ : 0 ≤ᵐ[volume.restrict C.domain] J)
    (hcontrol : Controls C.action (C.majorantMeasure J))
    (hmin : ∀ ν : Measure X, IsFiniteMeasure ν → Controls C.action ν →
      C.majorantMeasure J ≤ ν) :
    mass C.action = ∫ z, |(C.multiplicity z : ℝ)| * J z ∂volume.restrict C.domain := by
  have hfin : IsFiniteMeasure (C.majorantMeasure J) := densityPush_finite _ _ hρ
  have hνeq : (C.majorantMeasure J).real univ =
      ∫ z, |(C.multiplicity z : ℝ)| * J z ∂volume.restrict C.domain := by
    have hh := integral_densityPush (volume.restrict C.domain)
      C.measurable_paramExtended hρ
      (hJ.mono fun z hz => mul_nonneg (abs_nonneg _) hz) (continuous_const (y := (1:ℝ)))
    simpa only [majorantMeasure,integral_const,smul_eq_mul,mul_one] using hh
  rw [←hνeq]
  apply le_antisymm (mass_le_measure hfin hcontrol)
  obtain ⟨ν,hν,hνc,heq⟩ := hC.exists_controls_mass_eq
  rw [heq]
  exact ENNReal.toReal_mono (by let := hν; exact measure_ne_top ν univ)
    (hmin ν hν hνc univ)

theorem exists_radial_metric_mass (hX : IsCAT0 X) (hC : IsMetricCurrent C.action)
    (seg : X → X → ℝ → X)
    (hseg : ∀ o x a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o x b) = |a-b| *dist o x)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    ∃ p : Euc k → Seminorm ℝ (Euc k),
      (∀ v, Measurable (fun z => p z v)) ∧
      (∀ᵐ z ∂volume.restrict C.domain,
        (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
          C.domain C.param (p z) ⟨z,hz⟩) ∧
        (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
        (∀ v, p z v = 0 ↔ v = 0)) ∧
      mass C.action = (∫ z, |(C.multiplicity z : ℝ)| *Real.sqrt
        (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det
          ∂volume.restrict C.domain) ∧
      ∀ t ∈ Icc (0:ℝ) 1, (∀ y, 1-t*g y ∈ Icc (0:ℝ) 1) →
        Integrable (fun z => |(C.multiplicity z : ℝ)| *C.radialJacobian
          (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
          o g t z) (volume.restrict C.domain) ∧
        mass (pushCurrent (fun y => seg o y (1-t*g y)) C.action) ≤
          ∫ z, |(C.multiplicity z : ℝ)| *C.radialJacobian
            (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
            o g t z ∂volume.restrict C.domain := by
  obtain ⟨P,_,_,hρ,_,hcontrol,hmin,p,rfl,hpm,hp⟩ := C.exists_exact_quadratic_mass hX hC
  refine ⟨p,hpm,hp,C.mass_eq_integral_majorant hC hρ
    (Eventually.of_forall fun _ => Real.sqrt_nonneg _) hcontrol hmin,?_⟩
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuous.continuousOn
  let B : ℝ := max 1 (max (K:ℝ) (max M (Metric.diam (univ : Set X))))
  have hB : 1 ≤ B := le_max_left ..
  have hK : (K:ℝ) ≤ B := (le_max_left ..).trans (le_max_right ..)
  have hgb : ∀ x, |g x| ≤ B := by
    intro x
    have hm : |g x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x (mem_univ x)
    exact hm.trans ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..)))
  have hrb : ∀ x, dist o x ≤ B := by
    intro x
    exact (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)).trans
      ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))
  intro t ht htg
  have hrad := C.integrable_radialJacobian p hpm hp hρ o hg hB hK hgb hrb ht
  obtain ⟨L,hf⟩ := radial_lipschitzWith seg hseg hcomp o hg t htg
  exact ⟨hrad,C.radial_push_mass_le seg hcomp o g hg t htg hf p hp hrad⟩
end IntegerChart
end CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end
end

end OAI
