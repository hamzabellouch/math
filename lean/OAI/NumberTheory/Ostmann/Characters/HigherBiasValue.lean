import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFamily

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open scoped BigOperators

lemma translatedMean_norm_le_one {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    ‖translatedMean S χ a‖ ≤ 1 := by
  classical
  by_cases hS : S.Nonempty
  · have hcard : (S.card:ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
    have hsum : ‖∑ x∈S,χ (x-a)‖ ≤ (S.card:ℝ) := by
      calc
        _ ≤ ∑ x∈S,‖χ (x-a)‖ := norm_sum_le _ _
        _ ≤ ∑ _x∈S,(1:ℝ) := Finset.sum_le_sum (fun _ _ => norm_character_le_one _ _)
        _ = _ := by simp
    unfold translatedMean
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (inv_mul_cancel₀ hcard)
  · simp [translatedMean,Finset.not_nonempty_iff_eq_empty.mp hS]

lemma higherBias_le_one {p : ℕ} [Fact p.Prime] (S : Finset (ZMod p)) :
    (higherBias S:ℝ) ≤ 1 := by
  classical
  change higherBias S ≤ (1:NNReal)
  unfold higherBias
  apply Finset.sup_le
  intro q hq
  split_ifs
  · exact_mod_cast translatedMean_norm_le_one S q.1 q.2
  · positivity

def higherPrimeBias (d : Decomposition) (p : ℕ) : ℝ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    (higherBias (d.residueSupport p):ℝ)
  else 0

lemma higherPrimeBias_prime (d : Decomposition) (p : ℕ) [Fact p.Prime] :
    higherPrimeBias d p = (higherBias (d.residueSupport p):ℝ) := by
  simp [higherPrimeBias,Fact.out]

lemma higherPrimeBias_nonneg (d : Decomposition) (p : ℕ) : 0 ≤ higherPrimeBias d p := by
  unfold higherPrimeBias
  split_ifs <;> positivity

lemma higherPrimeBias_le_one (d : Decomposition) (p : ℕ) : higherPrimeBias d p ≤ 1 := by
  unfold higherPrimeBias
  split_ifs with hp
  · let : Fact p.Prime := ⟨hp⟩
    exact higherBias_le_one _
  · norm_num

end Ostmann.Characters

end

end OAI
