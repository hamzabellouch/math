import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductModel
import OAI.NumberTheory.CubicMoment.Estimates.MellinHeightTail

namespace OAI

/-! The complete complementary Mellin integral of the literal squarefree
product model. The actual inverse-sixth norm weight gives the correct
length power before rapid decay is applied. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem stopped_product_model_mellin_tail (hpnt : PrimaryPrimePNT)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (E U P B : Finset Eisenstein)
      (ψ : ℝ → ℝ) (w : ℝ) (remaining : Eisenstein → Prop)
      (β : Eisenstein → ℂ) (X Y M A T u : ℝ),
      (∀ e ∈ E, primary e) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      Real.exp 1 ≤ Y → 0 < X → 0 ≤ M → 0 < A → 0 < T →
      (∀ a ∈ P, primary a) → (∀ b ∈ B, primary b) →
      (∀ a ∈ P, ∀ b ∈ B, X ≤ norm (a*b) ∧ norm (a*b) ≤ Y) →
      (∀ b ∈ B, ‖β b‖ ≤ M) →
      ‖∫ τ in (Icc (-T) T)ᶜ, zeroLineMellinWeight V A τ*
        squarefreeProductModel P B (stoppedAlpha E U ψ w remaining) β (u-τ)‖ ≤
        (K*M*Y*X^(-1/6:ℝ)*(1+Real.log Y)^d/T^q)*
          (∫ τ : ℝ, |τ|^q*‖zeroLineMellinWeight V 1 τ‖) := by
  obtain ⟨K,d,hK,hbound⟩ := stopped_product_model_norm hpnt
  refine ⟨K,d,hK,?_⟩
  intro E U P B ψ w remaining β X Y M A T u hE hψ hY hX hM hA hT hP hB hn hβ
  have hY1 : 1 ≤ Y :=
    (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 1)).trans hY
  have hl : 0 ≤ 1+Real.log Y := by linarith [Real.log_nonneg hY1]
  have hm : 0 ≤ K*M*Y*X^(-1/6:ℝ)*(1+Real.log Y)^d := by positivity
  have hh := bounded_product_height_tail (zeroLineMellinWeight V A)
    (fun τ => squarefreeProductModel P B (stoppedAlpha E U ψ w remaining) β (u-τ))
    (zeroLineMellinWeight_integrable V hV hpos hsm hA) q
    (zeroLineMellinWeight_moment_integrable V hV hpos hsm hA q) hT hm
    (fun τ => hbound E U P B ψ w remaining β X Y M (u-τ)
      hE hψ hY hX hM hP hB hn hβ)
  have he : (∫ τ : ℝ, |τ|^q*‖zeroLineMellinWeight V A τ‖) =
      ∫ τ : ℝ, |τ|^q*‖zeroLineMellinWeight V 1 τ‖ := by
    apply integral_congr_ae
    filter_upwards with τ
    rw [zeroLineMellinWeight_norm V hA,
      zeroLineMellinWeight_norm V (by norm_num : (0:ℝ) < 1)]
  simpa only [he] using hh

end CubicFirstMoment

end

end OAI
