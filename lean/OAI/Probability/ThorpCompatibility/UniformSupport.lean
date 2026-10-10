import Mathlib
import OAI.Probability.ThorpCompatibility.Entropy
import OAI.Probability.ThorpCompatibility.EntropyBounds
import OAI.Probability.ThorpCompatibility.Prediction

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α]

lemma mean_neg (P : Law α) (f : α → ℝ) : P.mean (fun a => -f a) = -P.mean f := by
  simp [mean, Finset.sum_neg_distrib]

noncomputable def uniformOn (s : Finset α) (hs : s.Nonempty) : Law α where
  mass a := if a ∈ s then 1 / (s.card : ℝ) else 0
  nonneg a := by split_ifs <;> positivity
  total := by
    rw [← Finset.sum_filter]
    simp [hs.card_ne_zero]

lemma entropy_uniformOn_comparison (P : Law α) (s : Finset α) (hs : s.Nonempty)
    (hz : ∀ a, a ∉ s → P.mass a = 0) :
    P.relativeEntropy (uniformOn s hs) = Real.log (s.card : ℝ) - P.entropy := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  have hterm (a : α) : P.mass a * Real.log (P.mass a / (uniformOn s hs).mass a) =
      P.mass a * Real.log (P.mass a) + P.mass a * Real.log (s.card : ℝ) := by
    by_cases hp : P.mass a = 0
    · simp [hp]
    have ha : a ∈ s := by by_contra h; exact hp (hz a h)
    simp only [uniformOn, ite_eq_left ha, one_div, div_inv_eq_mul,
      Real.log_mul hp hc, mul_add]
  simp_rw [relativeEntropy, hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, P.total, one_mul]
  unfold entropy mean
  ring

lemma heavy_mass_uniformOn (P : Law α) (s : Finset α) (hs : s.Nonempty)
    (hz : ∀ a, a ∉ s → P.mass a = 0) {H : ℝ} (hH : 0 < H) :
    (Real.log H - 1) * P.prob (fun a => H / (s.card : ℝ) < P.mass a) ≤
      Real.log (s.card : ℝ) - P.entropy := by
  have hzero : ∀ a, (uniformOn s hs).mass a = 0 → P.mass a = 0 := by
    intro a h
    by_cases ha : a ∈ s
    · simp [uniformOn, ha, hs.card_ne_zero] at h
    · exact hz a ha
  have h := P.heavy_mass_bound (uniformOn s hs) hH hzero
  rw [P.entropy_uniformOn_comparison s hs hz] at h
  convert h using 2
  congr 1
  funext a
  apply propext
  by_cases ha : a ∈ s
  · simp [uniformOn, ha, div_eq_mul_inv]
  · have hb : 0 ≤ H / (s.card : ℝ) := div_nonneg hH.le (Nat.cast_nonneg _)
    simp [uniformOn, ha, hz a ha, not_lt.mpr hb]

lemma mean_prediction_entropy {β γ : Type*} [Fintype β] [Fintype γ]
    (P : Law α) (X : α → β) (Y : α → γ) :
    P.mean (fun a => (P.predict X Y (Y a)).entropy) = P.condEntropy X Y := by
  have h := P.mean_predict X Y (fun y b => -Real.log ((P.predict X Y y).mass b))
  simp only [mean_neg] at h
  rw [P.mean_predict_log, neg_neg] at h
  simpa only [entropy, mean_neg] using h

end Law
open Finset

end ThorpCompatibility

end OAI
