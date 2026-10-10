import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable

local instance sparseEntropyDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

def pathSubsets {E : Type*} [DecidableEq E] (k : ℕ) (F : Finset E) : Finset (Finset E) :=
  F.powerset.filter (fun S => F.card ≤ 2*S.card ∧ k ≤ F.card)

lemma path_entropy {E : Type*} [DecidableEq E] (k : ℕ) (F : Finset E)
    (q : ℝ) (hq : 0 ≤ q) (hqsmall : q ≤ 1/16) :
    (∑ S ∈ pathSubsets k F, q^S.card) ≤ (1/2:ℝ)^k := by
  by_cases hk : k ≤ F.card
  · have heach (S : Finset E) (hS : S ∈ pathSubsets k F) :
        q^S.card ≤ (1/4:ℝ)^F.card := by
      have hsize := (Finset.mem_filter.mp hS).2.1
      calc
        q^S.card ≤ (1/16:ℝ)^S.card := pow_le_pow_left₀ hq hqsmall _
        _ = (1/4:ℝ)^(2*S.card) := by rw [pow_mul]; norm_num
        _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hsize
    calc
      _ ≤ ∑ _S ∈ pathSubsets k F, (1/4:ℝ)^F.card := Finset.sum_le_sum heach
      _ = ((pathSubsets k F).card : ℝ)*(1/4:ℝ)^F.card := by simp
      _ ≤ (2:ℝ)^F.card*(1/4:ℝ)^F.card := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hc : (pathSubsets k F).card ≤ 2^F.card :=
          (Finset.card_filter_le _ _).trans_eq (Finset.card_powerset F)
        exact_mod_cast hc
      _ = (1/2:ℝ)^F.card := by rw [← mul_pow];norm_num
      _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  · have he : pathSubsets k F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      exact hk (Finset.mem_filter.mp hS).2.2
    rw [he,Finset.sum_empty]
    positivity

end SparseWitness

end

end OAI
