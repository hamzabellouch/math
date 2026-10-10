import OAI.NumberTheory.CubicMoment.Estimates.HeightConvolutionBound
import OAI.NumberTheory.CubicMoment.Estimates.ArithmeticMellinMoments

namespace OAI

/-! The actual radial Mellin kernel has enough integral moments to
transfer a bounded-window height mean through its full Mellin line. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

theorem arithmeticMellin_height_window (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q n : ℕ) :
    ∃ D₀ Dn : ℝ, 0 < D₀ ∧ 0 < Dn ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ (G : ℝ → ℝ), Continuous G → ∀ (E B S T u : ℝ),
      0 ≤ E → 0 ≤ B → 0 < S → 0 < T → (∀ t, ‖G t‖ ≤ E) →
      (∀ s, ‖s‖ ≤ S → dyadicHeightMean (fun t => G (t+u+s)) T ≤ B) →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖arithmeticMellinCoefficient M hM V hV hV' ρ s‖*G (t+u+s)) T ≤
        B*D₀+(2*E)/S^n*Dn := by
  obtain ⟨D₀,hD₀,hzero⟩ := arithmeticMellinCoefficient_moment_decay M hM V hV hV' q 0
  obtain ⟨Dn,hDn,hn⟩ := arithmeticMellinCoefficient_moment_decay M hM V hV hV' q n
  refine ⟨D₀,Dn,hD₀,hDn,?_⟩
  intro ρ hρ G hG E B S T u hE hB hS hT hbound hsmall
  let f := fun s => ‖arithmeticMellinCoefficient M hM V hV hV' ρ s‖
  have hi := dyadicHeightMean_convolution_window
    (arithmeticMellinCoefficient_continuous M hM V hV hV' ρ).norm
    (arithmeticMellinCoefficient_integrable M hM V hV hV' ρ).norm
    (fun _ => _root_.norm_nonneg _) hG hE hB hS hT hbound u n
    (arithmeticMellinCoefficient_moment_integrable M hM V hV hV' ρ n) hsmall
  have hz : (1+ρ)^q*(∫ s : ℝ, f s) ≤ D₀ := by
    simpa only [pow_zero,one_mul] using hzero ρ hρ
  calc
    _ ≤ (1+ρ)^q*(B*(∫ s : ℝ, f s)+(2*E)/S^n*(∫ s : ℝ, ‖s‖^n*f s)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = B*((1+ρ)^q*(∫ s : ℝ, f s))+
        (2*E)/S^n*((1+ρ)^q*(∫ s : ℝ, ‖s‖^n*f s)) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hz hB)
      (mul_le_mul_of_nonneg_left (hn ρ hρ) (by positivity))

theorem arithmeticMellin_signed_height_window (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q n : ℕ) :
    ∃ D₀ Dn : ℝ, 0 < D₀ ∧ 0 < Dn ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ (G : ℝ → ℝ), Continuous G → ∀ (E B S T u ε : ℝ),
      (ε = 1 ∨ ε = -1) → 0 ≤ E → 0 ≤ B → 0 < S → 0 < T →
      (∀ t, ‖G t‖ ≤ E) →
      (∀ s, ‖s‖ ≤ S → dyadicHeightMean (fun t => G (t+u+s)) T ≤ B) →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖arithmeticMellinCoefficient M hM V hV hV' ρ (ε*s)‖*G (t+u+s)) T ≤
        B*D₀+(2*E)/S^n*Dn := by
  obtain ⟨D₀,hD₀,hzero⟩ := arithmeticMellinCoefficient_moment_decay M hM V hV hV' q 0
  obtain ⟨Dn,hDn,hn⟩ := arithmeticMellinCoefficient_moment_decay M hM V hV hV' q n
  refine ⟨D₀,Dn,hD₀,hDn,?_⟩
  intro ρ hρ G hG E B S T u ε hε hE hB hS hT hbound hsmall
  let A := arithmeticMellinCoefficient M hM V hV hV' ρ
  have hc : Continuous A := arithmeticMellinCoefficient_continuous M hM V hV hV' ρ
  have hi : Integrable A := arithmeticMellinCoefficient_integrable M hM V hV hV' ρ
  have hmoment := arithmeticMellinCoefficient_moment_integrable M hM V hV hV' ρ n
  have hfi : Integrable (fun s => ‖A (ε*s)‖) := by
    rcases hε with rfl | rfl
    · simpa only [one_mul] using hi.norm
    · simpa only [neg_one_mul] using hi.norm.comp_neg
  have hfm : Integrable (fun s => ‖s‖^n*‖A (ε*s)‖) := by
    rcases hε with rfl | rfl
    · simpa only [one_mul] using hmoment
    · simpa only [neg_one_mul,norm_neg] using hmoment.comp_neg
  have heq (j : ℕ) : (∫ s : ℝ, ‖s‖^j*‖A (ε*s)‖) =
      ∫ s : ℝ, ‖s‖^j*‖A s‖ := by
    rcases hε with rfl | rfl
    · simp only [one_mul]
    · simpa only [neg_one_mul,norm_neg] using
        integral_neg_eq_self (fun s : ℝ => ‖s‖^j*‖A s‖) volume
  have hz : (1+ρ)^q*(∫ s : ℝ, ‖A (ε*s)‖) ≤ D₀ := by
    have he := heq 0
    simp only [pow_zero,one_mul] at he
    rw [he]
    simpa only [pow_zero,one_mul] using hzero ρ hρ
  have hnn : (1+ρ)^q*(∫ s : ℝ, ‖s‖^n*‖A (ε*s)‖) ≤ Dn := by
    rw [heq n]
    exact hn ρ hρ
  have hb := dyadicHeightMean_convolution_window
    ((hc.comp (show Continuous (fun s : ℝ => ε*s) from continuous_const.mul continuous_id)).norm)
    hfi (fun _ => _root_.norm_nonneg _) hG hE hB hS hT hbound u n hfm hsmall
  calc
    _ ≤ (1+ρ)^q*(B*(∫ s : ℝ, ‖A (ε*s)‖)+(2*E)/S^n*(∫ s : ℝ, ‖s‖^n*‖A (ε*s)‖)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = B*((1+ρ)^q*(∫ s : ℝ, ‖A (ε*s)‖))+
        (2*E)/S^n*((1+ρ)^q*(∫ s : ℝ, ‖s‖^n*‖A (ε*s)‖)) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hz hB)
      (mul_le_mul_of_nonneg_left hnn (by positivity))

end CubicFirstMoment

end

end OAI
