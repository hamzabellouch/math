import Mathlib
import OAI.Geometry.WeakHessian.Entropy.EntropyContact

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile220
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLocalWeakUpperGradient.geodesic_young_time_scaled
    {f D : X → ℝ} (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ} (hC : 0 < C) (t : Time) (ht : 0 < t.val) :
    (∫ γ,f (γ t)-f (γ timeZero) ∂π) ≤
      C/2*(∫ s in 0..t.val,∫ γ,(D (evalReal γ s))^2 ∂π)+
        t.val/(2*C)*(∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π) := by
  have H := (hD.const_mul (-C)).geodesic_young_time_local (hf.const_mul (-C)) hπ hb hgeo t ht
  have hleft : (∫ γ,(-C)*f (γ timeZero)-(-C)*f (γ t) ∂π) =
      C*(∫ γ,f (γ t)-f (γ timeZero) ∂π) := by
    rw [← integral_const_mul]
    congr 1; funext γ; ring
  have hs (s : ℝ) : (∫ γ,(|-C| *D (evalReal γ s))^2 ∂π) =
      C^2*(∫ γ,(D (evalReal γ s))^2 ∂π) := by
    simp only [abs_neg,abs_of_pos hC,mul_pow,integral_const_mul]
  rw [hleft] at H
  simp_rw [hs] at H
  rw [intervalIntegral.integral_const_mul] at H
  have H' := div_le_div_of_nonneg_right H hC.le
  rw [mul_div_cancel_left₀ _ hC.ne'] at H'
  calc
    _ ≤ _ := H'
    _ = _ := by field_simp [hC.ne']
end WeakHessian

end
end InlinedFile220

end OAI
