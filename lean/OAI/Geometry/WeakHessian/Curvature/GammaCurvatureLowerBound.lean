import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.BochnerConvex

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile194
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma gamma_curvature_lower_bound (hfin : FiniteOnBoundedSets m)
    {u ξ k : X → ℝ} (hu : Sobolev m u)
    (hξm : AEStronglyMeasurable ξ m) {Cξ : ℝ} (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂m,0 ≤ ξ x) (hkm : AEStronglyMeasurable k m)
    {Ck k0 : ℝ} (hkb : ∀ᵐ x ∂m,|k x| ≤ Ck) (hk0 : ∀ᵐ x ∂m,k0 ≤ k x) :
    k0*(∫ x,ξ x*gamma m u u x ∂m) ≤ ∫ x,(ξ x*k x)*gamma m u u x ∂m := by
  have hi := integrable_bounded_gamma hfin hu hu hξm hξb
  have hj := hi.bdd_mul hkm (by simpa only [Real.norm_eq_abs] using hkb)
  have he : (fun x => k x*(ξ x*gamma m u u x)) = (fun x => (ξ x*k x)*gamma m u u x) := by funext x; ring
  have hj' : Integrable (fun x => (ξ x*k x)*gamma m u u x) m := by simpa only [he] using hj
  rw [← integral_const_mul]
  apply integral_mono_ae (hi.const_mul k0) hj'
  filter_upwards [hξ0,hk0,gamma_self (m := m) u] with x hξ hk hΓ
  rw [hΓ]
  nlinarith [mul_nonneg (sub_nonneg.mpr hk) (mul_nonneg hξ (sq_nonneg (weakGradient m u x)))]
end WeakHessian

end
end InlinedFile194

end OAI
