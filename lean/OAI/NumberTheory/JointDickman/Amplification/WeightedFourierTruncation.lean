import OAI.NumberTheory.JointDickman.Amplification.FourierProfileTail

namespace OAI

/-! # Extending a bounded endpoint product from a finite frequency interval -/

namespace JointDickman
open MeasureTheory Set
open scoped SchwartzMap

theorem schwartz_weighted_truncation (w : 𝓢(ℝ,ℝ)) (F : ℝ → ℂ)
    (hF : Continuous F) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 < R)
    (hbound : ∀ ξ, ‖F ξ‖ ≤ M) (k : ℕ) :
    ‖(∫ ξ : ℝ, testFourierTransform w ξ*F ξ)-
      (∫ ξ in -R..R, testFourierTransform w ξ*F ξ)‖ ≤
      M*(R^k)⁻¹*(∫ ξ : ℝ, |ξ|^k*‖testFourierTransform w ξ‖) := by
  let f := fun ξ : ℝ => testFourierTransform w ξ*F ξ
  have hf : Integrable f := (schwartz_testFourier_integrable w).mul_bdd
    hF.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hsplit := integral_add_compl (s := Icc (-R) R) measurableSet_Icc hf
  have hi : (∫ ξ in -R..R, f ξ) = ∫ ξ in Icc (-R) R, f ξ := by
    rw [intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]
  have hs : (Icc (-R) R)ᶜ = {ξ : ℝ | R < |ξ|} := by
    ext ξ
    simp only [mem_compl_iff,mem_Icc,mem_ofPred_eq,not_and_or,not_le,lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
  change ‖(∫ ξ : ℝ, f ξ)-(∫ ξ in -R..R, f ξ)‖ ≤ _
  rw [hi,← hsplit,add_sub_cancel_left,hs]
  calc
    _ ≤ ∫ ξ in {ξ : ℝ | R < |ξ|}, M*‖testFourierTransform w ξ‖ := by
      apply norm_integral_le_of_norm_le ((schwartz_testFourier_integrable w).norm.const_mul M).integrableOn
      filter_upwards [] with ξ
      dsimp [f]
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hbound ξ) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = M*(∫ ξ in {ξ : ℝ | R < |ξ|}, ‖testFourierTransform w ξ‖) := integral_const_mul _ _
    _ ≤ M*((R^k)⁻¹*(∫ ξ : ℝ, |ξ|^k*‖testFourierTransform w ξ‖)) :=
      mul_le_mul_of_nonneg_left (schwartz_testFourier_tail w k hR) hM
    _ = _ := by ring

end JointDickman

end OAI
