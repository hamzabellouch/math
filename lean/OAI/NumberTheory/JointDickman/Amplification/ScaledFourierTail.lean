import OAI.NumberTheory.JointDickman.Amplification.FullSmallArcModel

namespace OAI

/-! # The frequency tail after freezing the coefficient density -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap

theorem testFourierTransform_smul (c : ℝ) (w : 𝓢(ℝ,ℝ)) (ξ : ℝ) :
    testFourierTransform (⇑(c • w : 𝓢(ℝ,ℝ))) ξ = (c : ℂ)*testFourierTransform w ξ := by
  unfold testFourierTransform
  change (∫ s : ℝ, ((c*w s : ℝ) : ℂ)*additivePhase (-ξ*s)) =
    (c : ℂ)*(∫ s : ℝ, (w s : ℂ)*additivePhase (-ξ*s))
  simp only [Complex.ofReal_mul,mul_assoc]
  exact integral_const_mul _ _

theorem frozen_model_tail_error {B j : ℕ} [NeZero j] (hB : 0 < B)
    (X : ℝ) (Q : ℕ) (F : ℝ → ℂ) (hF : Continuous F)
    (w : 𝓢(ℝ,ℝ)) (d : ℝ) (a : ℕ+ → ℂ) (ha : ∀ q, ‖a q‖ ≤ 1)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, ‖F x‖ ≤ M) (k : ℕ) :
    ‖fullSmallMajorArcModel B j X Q F (fun ξ => (d : ℂ)*testFourierTransform w ξ) a-
      smallMajorArcModel B j X Q F (fun ξ => (d : ℂ)*testFourierTransform w ξ) a‖ ≤
      ((B^12 : ℕ) : ℝ)*((B^12 : ℕ)+1)*
        (M*(((B : ℝ)^13)^k)⁻¹*|d| *(∫ ξ : ℝ, |ξ|^k*‖testFourierTransform w ξ‖)) := by
  have he := smallArcModel_full_error (j := j) hB X Q F hF (d • w) a ha hM hbound k
  have hscale : testFourierTransform (⇑(d • w : 𝓢(ℝ,ℝ))) = fun ξ => (d : ℂ)*testFourierTransform w ξ :=
    funext (testFourierTransform_smul d w)
  rw [hscale] at he
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs] at he
  have hi : (∫ ξ : ℝ, |ξ|^k*(|d| *‖testFourierTransform w ξ‖)) =
      |d| *(∫ ξ : ℝ, |ξ|^k*‖testFourierTransform w ξ‖) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ξ => by ring)
  rw [hi] at he
  exact he.trans_eq (by ring)

end JointDickman

end OAI
