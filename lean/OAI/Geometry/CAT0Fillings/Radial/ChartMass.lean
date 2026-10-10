import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Extensions
import OAI.Geometry.CAT0Fillings.Currents.Pushforward
import OAI.Geometry.CAT0Fillings.Currents.PushMajorant
import OAI.Geometry.CAT0Fillings.Radial.TestBound

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
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] {k : ℕ} (C : IntegerChart X k)
noncomputable def radialJacobian (P : Euc k → Matrix (Fin k) (Fin k) ℝ)
    (o : X) (g : X → ℝ) (t : ℝ) (z : Euc k) : ℝ :=
  Real.sqrt (metricSpatialRadialForm (P z) (C.scalar g z)
    (C.scalar (dist o) z) t
    (differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z))
    (differentialRow (fderivWithin ℝ (C.scalar g) C.domain z))).det

omit [MeasurableSpace X] [BorelSpace X] in
theorem ae_radial_jacobian_bound
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) (g : X → ℝ) {Kg Kf : ℝ≥0} (hg : LipschitzWith Kg g)
    (t : ℝ) (htg : ∀ y, 1-t*g y ∈ Icc (0:ℝ) 1)
    (hf : LipschitzWith Kf (fun y => seg o y (1-t*g y)))
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (π : Fin k → X → ℝ) (hπ : ∀ i, LipschitzWith 1 (π i)) :
    ∀ᵐ z ∂volume.restrict C.domain,
      |C.jacobian (fun i y => π i (seg o y (1-t*g y))) z| ≤
        C.radialJacobian
          (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
          o g t z := by
  have htests : ∀ᵐ z ∂volume.restrict C.domain, ∀ i,
      DifferentiableWithinAt ℝ (C.scalar (fun y => π i (seg o y (1-t*g y))))
        C.domain z := ae_all_iff.mpr fun i =>
    C.ae_differentiableWithinAt_scalar ((hπ i).comp hf)
  filter_upwards [hp,ae_restrict_mem C.borel,
    Besicovitch.ae_tendsto_measure_inter_div volume C.domain,
    C.ae_differentiableWithinAt_scalar (LipschitzWith.dist_right o),
    C.ae_differentiableWithinAt_scalar hg,htests] with z hpz hzs hden hr hgz htests
  have hpe : (fun y => dist (C.paramExtended y) (C.paramExtended z)-p z (y-z))
      =o[𝓝[C.domain] z] (fun y => y-z) := by
    rw [nhdsWithin_eq_map_subtype_coe hzs,Asymptotics.isLittleO_map]
    have hh := hpz.1 hzs
    change (fun y : C.domain => dist (C.param y) (C.param ⟨z,hzs⟩)-
      p z ((y : Euc k)-z)) =o[𝓝 (⟨z,hzs⟩ : C.domain)]
      (fun y : C.domain => (y : Euc k)-z) at hh
    convert hh using 1
    · ext y
      simp only [Function.comp_apply,paramExtended,dite_eq_left y.property,dite_eq_left hzs,
        Subtype.coe_eta]
    · rfl
  have heq (b : X → ℝ) : EqOn (fun y => b (C.paramExtended y)) (C.scalar b) C.domain := by
    intro y hy
    simp only [paramExtended,scalar,dite_eq_left hy]
  have hR := hr.hasFDerivWithinAt.congr (heq (dist o)) (heq (dist o) hzs)
  have hG := hgz.hasFDerivWithinAt.congr (heq g) (heq g hzs)
  have hh := radial_test_det_le seg hcomp hzs hden C.paramExtended o (p z) hpe
    hpz.2.2 hpz.2.1 (fun y => g (C.paramExtended y)) t (fun y _ => htg _)
    (fderivWithin ℝ (C.scalar (dist o)) C.domain z)
    (fderivWithin ℝ (C.scalar g) C.domain z) hR hG
    (fun i => C.scalar (fun y => π i (seg o y (1-t*g y))))
    (fun i => fderivWithin ℝ (C.scalar (fun y => π i (seg o y (1-t*g y)))) C.domain z)
    (fun i => (htests i).hasFDerivWithinAt) π hπ (by
      intro i y hy
      simp only [paramExtended,scalar,dite_eq_left hy])
  convert hh using 1
  · congr 2
  · simp only [radialJacobian,←heq g hzs,←heq (dist o) hzs]

theorem radial_push_mass_le
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) (g : X → ℝ) {Kg Kf : ℝ≥0} (hg : LipschitzWith Kg g)
    (t : ℝ) (htg : ∀ y, 1-t*g y ∈ Icc (0:ℝ) 1)
    (hf : LipschitzWith Kf (fun y => seg o y (1-t*g y)))
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| *
      C.radialJacobian
        (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
        o g t z) (volume.restrict C.domain)) :
    mass (pushCurrent (fun y => seg o y (1-t*g y)) C.action) ≤
      ∫ z, |(C.multiplicity z : ℝ)| *
        C.radialJacobian
          (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
          o g t z ∂volume.restrict C.domain := by
  apply C.push_mass_le_majorant hf hρ
    (Eventually.of_forall fun _ => Real.sqrt_nonneg _)
  intro π hπ
  exact C.ae_radial_jacobian_bound seg hcomp o g hg t htg hf p hp π hπ
end IntegerChart
end CAT0Fillings

end
end

end OAI
