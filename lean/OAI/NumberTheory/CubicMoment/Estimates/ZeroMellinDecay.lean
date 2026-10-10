import OAI.NumberTheory.CubicMoment.Estimates.MellinHeightTail

namespace OAI

/-! Uniform decay in the total-product scale on the zero Mellin line. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma continuous_norm_zeroLineMellinWeight (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) {X : ℝ} (hX : 0 < X) :
    Continuous (fun t => ‖zeroLineMellinWeight W X t‖) := by
  have he : (fun t => ‖zeroLineMellinWeight W X t‖) =
      fun t => (1/(2*Real.pi))*‖mellinVerticalSchwartz W hW hpos hsm 0 t‖ := by
    funext t
    rw [zeroLineMellinWeight_norm W hX,mellinVerticalSchwartz_apply]
    simp only [Complex.ofReal_zero,zero_add]
  rw [he]
  exact continuous_const.mul (mellinVerticalSchwartz W hW hpos hsm 0).continuous.norm

theorem zeroLineMellinWeight_decay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 < X → ∀ t : ℝ, t ≠ 0 →
      ‖zeroLineMellinWeight W X t‖ ≤ C/|t|^n := by
  obtain ⟨C,hC,hb⟩ := smooth_mellin_vertical_decay W hW hpos hsm 0 n
  refine ⟨C/(2*Real.pi),by positivity,?_⟩
  intro X hX t ht
  have hat : 0 < |t| := abs_pos.mpr ht
  apply (le_div_iff₀ (pow_pos hat n)).mpr
  rw [zeroLineMellinWeight_norm W hX]
  have hp : |t|^n*‖mellin W ((t:ℂ)*Complex.I)‖ ≤ C := by
    apply le_trans _ (by simpa only [Complex.ofReal_zero,zero_add] using hb t)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg t) (by linarith : |t| ≤ 1+|t|) n) (_root_.norm_nonneg _)
  convert mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 1/(2*Real.pi)) using 1 <;> ring

end CubicFirstMoment

end

end OAI
