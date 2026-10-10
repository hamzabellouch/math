import OAI.NumberTheory.TwoPoint.Bounds.ShiftTransfer
import OAI.NumberTheory.TwoPoint.Bounds.RoughShiftBoundary

namespace OAI

/-! Setting the unused value at zero to zero permits globally bounded graph
test vectors without changing any of the theorem's positive correlations. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def positiveNormalization (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else f n

lemma positiveNormalization_eq {f : ℕ → ℂ} {n : ℕ} (hn : 0 < n) :
    positiveNormalization f n = f n := by
  simp only [positiveNormalization, ne_of_gt hn, ite_false]

lemma positiveNormalization_norm {f : ℕ → ℂ} (hf : OneBounded f) (n : ℕ) :
    ‖positiveNormalization f n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [positiveNormalization, hn]
  · rw [positiveNormalization_eq (Nat.pos_of_ne_zero hn)]
    exact hf n (Nat.pos_of_ne_zero hn)

lemma Multiplicative.positiveNormalization {f : ℕ → ℂ} (hf : Multiplicative f) :
    Multiplicative (positiveNormalization f) := by
  intro m n hm hn hcop
  rw [positiveNormalization_eq (Nat.mul_pos hm hn), positiveNormalization_eq hm,
    positiveNormalization_eq hn]
  exact hf m n hm hn hcop

lemma UniformlyNonpretentious.positiveNormalization {f : ℕ → ℂ}
    (hnp : UniformlyNonpretentious f) (hf : OneBounded f) :
    UniformlyNonpretentious (positiveNormalization f) := by
  apply hnp.finite_prime_change ∅ hf (fun n _ => positiveNormalization_norm hf n)
  intro p hp _
  exact positiveNormalization_eq hp.pos

lemma positiveNormalization_prefix (f g : ℕ → ℂ) (h N : ℕ) :
    positivePrefix (fun n => positiveNormalization f n * positiveNormalization g (n + h)) N =
      positivePrefix (fun n => f n * g (n + h)) N := by
  unfold positivePrefix
  apply sum_congr rfl
  intro n _
  dsimp only
  rw [positiveNormalization_eq (by omega), positiveNormalization_eq (by omega)]

lemma correlationSum_eq_positivePrefix (f g : ℕ → ℂ) (h N : ℕ) :
    correlationSum f g 0 h N = positivePrefix (fun n => f n * g (n + h)) N := by
  unfold correlationSum positivePrefix
  simp only [Nat.add_zero]
  rw [← Ico_add_one_right_eq_Icc, ← zero_add 1,
    ← sum_Ico_add' (fun n => f n * g (n + h)) 0 N 1, range_eq_Ico]

end TwoPointCorrelations

end OAI
