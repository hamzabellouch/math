import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CompContDiff2

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integral_exponentialMeasure {V : X → ℝ} (hV : AEMeasurable V m) (f : X → ℝ) :
    (∫ x, f x ∂exponentialMeasure m V) = ∫ x, Real.exp (V x)*f x ∂m := by
  have H := integral_withDensity_eq_integral_toReal_smul₀
    (Real.measurable_exp.comp_aemeasurable hV).ennreal_ofReal
    (ae_of_all m fun _ => ENNReal.ofReal_lt_top) f
  simpa only [exponentialMeasure,Function.comp_apply,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul] using H

lemma IsLaplacian.reweight (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A V : X → ℝ}
    (hA : IsLaplacian m u A) {L : ℝ≥0} (hV : LipschitzWith L V)
    {B : ℝ} (hB : ∀ x, |V x| ≤ B) :
    IsLaplacian (exponentialMeasure m V) u (fun x => A x+gamma m V u x) := by
  obtain ⟨_,hν⟩ := exponentialMeasure_comparable (m := m) hB
  have hu := hA.1
  have hVu := memLp_gamma_of_lipschitz hfinite hpar hV hu
  refine ⟨(sobolev_exponentialMeasure_iff hB u).mp hu,
    MemLp.of_measure_le_smul ENNReal.ofReal_ne_top hν (hA.2.1.add hVu), ?_⟩
  intro v hvν
  have hv := (sobolev_exponentialMeasure_iff hB v).mpr hvν
  have hb : ∀ᵐ x ∂m, V x ≤ B := ae_of_all m fun x => (le_abs_self _).trans (hB x)
  have heb : ∀ᵐ x ∂m, ‖Real.exp (V x)‖ ≤ Real.exp B := by
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx
  have hem := (Real.continuous_exp.comp hV.continuous).aestronglyMeasurable (μ := m)
  have hig : Integrable (fun x => Real.exp (V x)*gamma m u v x) m :=
    (integrable_gamma hfinite hu hv).bdd_mul hem heb
  have hiD : Integrable (fun x => Real.exp (V x)*(gamma m V u x*v x)) m :=
    (hVu.integrable_mul hv.1).bdd_mul hem heb
  have hiA : Integrable (fun x => Real.exp (V x)*(A x*v x)) m :=
    (hA.2.1.integrable_mul hv.1).bdd_mul hem heb
  have htest := hA.2.2 (fun x => v x*Real.exp (V x)) (hv.mul_exp hfinite hV hb)
  have heq : gamma m u (fun x => v x*Real.exp (V x)) =ᵐ[m]
      (fun x => Real.exp (V x)*gamma m u v x + Real.exp (V x)*(gamma m V u x*v x)) := by
    filter_upwards [gamma_mul_exp_left hfinite hpar hv.2.1
      (localSobolev_of_lipschitz hfinite hV) hu.2.1 hb
      (weakGradient_le_lipschitz hfinite hV),
      gamma_comm (m := m) u (fun x => v x*Real.exp (V x)),gamma_comm (m := m) v u]
      with x hp hc hcv
    rw [hc,hp,hcv]
    ring
  rw [integral_congr_ae heq, integral_add hig hiD] at htest
  have heA : (∫ x, A x*(v x*Real.exp (V x)) ∂m) =
      ∫ x, Real.exp (V x)*(A x*v x) ∂m := by
    congr 1
    funext x
    ring
  rw [heA] at htest
  have hg := gamma_exponentialMeasure (m := m) hB u v
  rw [integral_exponentialMeasure hV.continuous.aemeasurable,
    integral_exponentialMeasure hV.continuous.aemeasurable]
  calc
    (∫ x, Real.exp (V x)*gamma (exponentialMeasure m V) u v x ∂m) =
        ∫ x, Real.exp (V x)*gamma m u v x ∂m :=
      integral_congr_ae (by filter_upwards [hg] with x hx; rw [hx])
    _ = -(∫ x, Real.exp (V x)*(A x*v x) ∂m) -
        (∫ x, Real.exp (V x)*(gamma m V u x*v x) ∂m) := by linarith
    _ = -(∫ x, Real.exp (V x)*((A x+gamma m V u x)*v x) ∂m) := by
      rw [show (fun x => Real.exp (V x)*((A x+gamma m V u x)*v x)) =
        (fun x => Real.exp (V x)*(A x*v x)+ Real.exp (V x)*(gamma m V u x*v x)) by
          funext x; ring,integral_add hiA hiD]
      ring
end WeakHessian

end
end InlinedFile0

end OAI
