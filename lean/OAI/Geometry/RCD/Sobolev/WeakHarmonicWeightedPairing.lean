import OAI.Geometry.RCD.Sobolev.LocalLipschitzGreenTrace
import OAI.Geometry.RCD.Sobolev.EuclideanWeakHarmonicSmoothing

namespace OAI

/-! # A weighted gradient identity for the Euclidean harmonic limit -/

open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ContDiff NNReal
noncomputable section
namespace RegularPointCoordinates

theorem weak_harmonic_weighted_pairing {n : ℕ} {S : ℝ} (hS : 0<S)
    {g q ψ : Euclidean n → ℝ}
    (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hweak : EuclideanWeakHarmonicOn g S) (hq : ContDiff ℝ ∞ q)
    (hψ : InteriorSmoothTest n S ψ)
    (h₁ : Integrable (fun x => q x*inner ℝ (gradient ψ x) (gradient g x)) volume)
    (h₂ : Integrable (fun x => ψ x*inner ℝ (gradient q x) (gradient g x)) volume) :
    (∫ x, q x*inner ℝ (gradient ψ x) (gradient g x))=
      -(∫ x, ψ x*inner ℝ (gradient q x) (gradient g x)) := by
  have htest : InteriorSmoothTest n S (fun x => q x*ψ x) :=
    ⟨hq.mul hψ.1,hψ.2.1.mul_left,tsupport_mul_subset_right.trans hψ.2.2⟩
  have hgreen := local_lipschitz_green_trace hS hg htest
  rw [hweak _ htest,neg_zero] at hgreen
  have hpoint (x : Euclidean n) :
      inner ℝ (gradient g x) (gradient (fun y => q y*ψ y) x)=
        q x*inner ℝ (gradient ψ x) (gradient g x)+
          ψ x*inner ℝ (gradient q x) (gradient g x) := by
    conv_lhs => rw [real_inner_comm]
    simp only [inner_gradient_left]
    rw [fderiv_fun_mul (hq.differentiable (by simp) x) (hψ.1.differentiable (by simp) x)]
    rfl
  rw [integral_congr_ae (Eventually.of_forall hpoint),integral_add h₁ h₂] at hgreen
  linarith

end RegularPointCoordinates

end

end OAI
