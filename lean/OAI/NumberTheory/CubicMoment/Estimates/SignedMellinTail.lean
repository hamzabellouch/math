import OAI.NumberTheory.CubicMoment.Estimates.DyadicMellinTail

namespace OAI

/-! Both signs of the height variable in the low-core Mellin integral. -/
noncomputable section
open Set Filter MeasureTheory
namespace CubicFirstMoment

theorem signed_height_mean_positive {g : ℝ → ℝ} (_hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    {T B : ℝ} (hT : 0 < T)
    (hmean : ∀ S : ℝ, T ≤ S →
      ((∫ t in S..2*S, g t)+(∫ t in -2*S..-S, g t))/S ≤ B) :
    ∀ S : ℝ, T ≤ S → (∫ t in S..2*S, g t) ≤ B*S := by
  intro S hTS
  have hS : 0 < S := hT.trans_le hTS
  have hn : 0 ≤ ∫ t in -2*S..-S, g t :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => hg0 t)
  have hm := (div_le_iff₀ hS).mp (hmean S hTS)
  linarith

theorem signed_height_mean_negative {g : ℝ → ℝ} (_hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    {T B : ℝ} (hT : 0 < T)
    (hmean : ∀ S : ℝ, T ≤ S →
      ((∫ t in S..2*S, g t)+(∫ t in -2*S..-S, g t))/S ≤ B) :
    ∀ S : ℝ, T ≤ S → (∫ t in S..2*S, g (-t)) ≤ B*S := by
  intro S hTS
  have hS : 0 < S := hT.trans_le hTS
  have hn : 0 ≤ ∫ t in S..2*S, g t :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => hg0 t)
  have hm := (div_le_iff₀ hS).mp (hmean S hTS)
  rw [intervalIntegral.integral_comp_neg]
  have he : -(2*S) = -2*S := by ring
  rw [he]
  linarith

theorem weighted_signed_mellin_tail {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hg0 : ∀ t, 0 ≤ g t) (hfg : Integrable (fun t => f t*g t))
    {T B C : ℝ} (hT : 0 < T) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmean : ∀ S : ℝ, T ≤ S →
      ((∫ t in S..2*S, g t)+(∫ t in -2*S..-S, g t))/S ≤ B)
    (hdecay : ∀ t : ℝ, T ≤ |t| → f t ≤ C/t^2) :
    ((∫ t in Ici T, f t*g t)+(∫ t in Ici T, f (-t)*g (-t))) ≤ 4*B*C/T := by
  have hp := weighted_positive_mellin_tail hf hg hg0 hfg hT hB hC
    (signed_height_mean_positive hg hg0 hT hmean) (fun t ht =>
      hdecay t (by rw [abs_of_pos (hT.trans_le ht)]; exact ht))
  have hi : Integrable (fun t : ℝ => f (-t)*g (-t)) :=
    (MeasurePreserving.integrable_comp_emb (Measure.measurePreserving_neg volume)
      (Homeomorph.neg ℝ).measurableEmbedding).mpr hfg
  have hn := weighted_positive_mellin_tail (hf.comp continuous_neg) (hg.comp continuous_neg)
    (fun t => hg0 (-t)) hi hT hB hC (signed_height_mean_negative hg hg0 hT hmean)
    (fun t ht => by
      have hh := hdecay (-t) (by rw [abs_neg,abs_of_pos (hT.trans_le ht)]; exact ht)
      simpa only [Function.comp_apply,neg_sq] using hh)
  calc
    _ ≤ 2*B*C/T+2*B*C/T := add_le_add hp hn
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
