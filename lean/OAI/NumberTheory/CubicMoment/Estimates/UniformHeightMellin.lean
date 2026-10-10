import OAI.NumberTheory.CubicMoment.Estimates.HeightConvolution
import OAI.NumberTheory.CubicMoment.Estimates.ArithmeticMellinMoments

namespace OAI

/-! A translation-uniform height mean passes through the whole Mellin
line without truncation. All interchanges follow from absolute Fubini. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma dyadicHeightMean_convolution_uniform {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hf0 : ∀ s, 0 ≤ f s)
    (hG : Continuous G) {M B T : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M)
    (hT : 0 < T) (hmean : ∀ v, dyadicHeightMean (fun t => G (t+v)) T ≤ B) (u : ℝ) :
    dyadicHeightMean (fun t => ∫ s : ℝ, f s*G (t+u+s)) T ≤ B*(∫ s : ℝ, f s) := by
  rw [dyadicHeightMean_convolution hf hfi hG hbound u hT]
  have hp := integrable_height_convolution_interval hf hfi hG hbound u
    (by linarith : T ≤ 2*T)
  have hn := integrable_height_convolution_interval hf hfi hG hbound u
    (by linarith : -2*T ≤ -T)
  have hi : Integrable (fun s => f s*dyadicHeightMean (fun t => G (t+u+s)) T) := by
    convert (hp.add hn).div_const T using 1
    funext s
    dsimp [dyadicHeightMean]
    ring
  have hm := integral_mono hi (hfi.mul_const B) (fun s => by
    apply mul_le_mul_of_nonneg_left _ (hf0 s)
    simpa only [add_assoc] using hmean (u+s))
  exact hm.trans_eq (by rw [integral_mul_const]; ring)

/-- Both signs of the arithmetic Mellin coefficient have the same full
line bound. The sole cost is its already proved zeroth moment. -/
theorem arithmeticMellin_signed_height_uniform (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ (G : ℝ → ℝ), Continuous G → ∀ (E B T u ε : ℝ),
      (ε = 1 ∨ ε = -1) → 0 ≤ B → 0 < T → (∀ t, ‖G t‖ ≤ E) →
      (∀ v, dyadicHeightMean (fun t => G (t+v)) T ≤ B) →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖arithmeticMellinCoefficient M hM V hV hV' ρ (ε*s)‖*G (t+u+s)) T ≤ D*B := by
  obtain ⟨D,hD,hdecay⟩ := arithmeticMellinCoefficient_moment_decay M hM V hV hV' q 0
  refine ⟨D,hD,?_⟩
  intro ρ hρ G hG E B T u ε hε hB hT hbound hmean
  let A := arithmeticMellinCoefficient M hM V hV hV' ρ
  have hc : Continuous A := arithmeticMellinCoefficient_continuous M hM V hV hV' ρ
  have hi : Integrable A := arithmeticMellinCoefficient_integrable M hM V hV hV' ρ
  have hfi : Integrable (fun s => ‖A (ε*s)‖) := by
    rcases hε with rfl | rfl
    · simpa only [one_mul] using hi.norm
    · simpa only [neg_one_mul] using hi.norm.comp_neg
  have heq : (∫ s : ℝ, ‖A (ε*s)‖) = ∫ s : ℝ, ‖A s‖ := by
    rcases hε with rfl | rfl
    · simp only [one_mul]
    · simpa only [neg_one_mul] using integral_neg_eq_self (fun s : ℝ => ‖A s‖) volume
  have hd : (1+ρ)^q*(∫ s : ℝ, ‖A (ε*s)‖) ≤ D := by
    rw [heq]
    simpa only [pow_zero,one_mul] using hdecay ρ hρ
  have hb := dyadicHeightMean_convolution_uniform
    (hc.comp (show Continuous (fun s : ℝ => ε*s) from continuous_const.mul continuous_id)).norm
    hfi (fun _ => _root_.norm_nonneg _) hG hbound hT hmean u
  calc
    _ ≤ (1+ρ)^q*(B*(∫ s : ℝ, ‖A (ε*s)‖)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = B*((1+ρ)^q*(∫ s : ℝ, ‖A (ε*s)‖)) := by ring
    _ ≤ B*D := mul_le_mul_of_nonneg_left hd hB
    _ = _ := mul_comm _ _

end CubicFirstMoment

end

end OAI
