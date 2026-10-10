import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

namespace ErdosRandomVariance
attribute [local instance] Classical.propDecidable

noncomputable def congruenceIndicator (d i j : ℕ) : ℝ := if Nat.ModEq d i j then 1 else 0

theorem congruenceIndicator_symm (d i j : ℕ) :
    congruenceIndicator d i j = congruenceIndicator d j i := by
  have he : Nat.ModEq d i j ↔ Nat.ModEq d j i := ⟨fun h => h.symm, fun h => h.symm⟩
  simp only [congruenceIndicator, he]

theorem residue_indicator_sum (J d a : ℕ) :
    (∑ i ∈ Finset.range J, congruenceIndicator d i a) =
      (((Finset.range J).filter (fun i => Nat.ModEq d i a)).card : ℝ) := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    congruenceIndicator]

theorem residue_indicator_bound (J d a : ℕ) (hd : 0 < d) :
    (∑ i ∈ Finset.range J, congruenceIndicator d i a) ≤ (J : ℝ)/d+1 := by
  rw [residue_indicator_sum]
  have hc : ((Finset.range J).filter (fun i => Nat.ModEq d i a)).card ≤ J/d+1 := by
    rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card J hd a]
    split_ifs <;> omega
  have hcr : (((Finset.range J).filter (fun i => Nat.ModEq d i a)).card : ℝ) ≤
      (J/d : ℕ)+1 := by exact_mod_cast hc
  have hdiv : ((J/d : ℕ) : ℝ) ≤ (J : ℝ)/d := by
    apply (le_div_iff₀ (show (0 : ℝ) < d by exact_mod_cast hd)).mpr
    exact_mod_cast Nat.div_mul_le_self J d
  linarith

theorem interval_pair_congruence_bound (J d : ℕ) (hd : 0 < d) :
    (∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, congruenceIndicator d i j) ≤
      (J : ℝ)^2/d+J := by
  calc
    _ = ∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, congruenceIndicator d j i := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congruenceIndicator_symm d i j
    _ ≤ ∑ _i ∈ Finset.range J, ((J : ℝ)/d+1) :=
      Finset.sum_le_sum (fun i _ => residue_indicator_bound J d i hd)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end ErdosRandomVariance

end

end Erdos970

end OAI
