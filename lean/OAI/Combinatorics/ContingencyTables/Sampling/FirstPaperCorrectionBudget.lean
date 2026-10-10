import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperBinaryParameters

namespace OAI

/-! # Cardinality and rare-branch precision for exact correction -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators
open CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J]

noncomputable def correctionPrecision (r : I → ℕ) (c : J → ℕ) : ℕ :=
  (dimensionAllowance (I := I) (J := J))^6*(smallBinaryLength r c)^2

lemma table_card_binary_bound (r : I → ℕ) (c : J → ℕ) :
    Fintype.card (Table r c)≤
      2^((dimensionAllowance (I := I) (J := J))*smallBinaryLength r c) := by
  have hn : (∑ i,r i)+1≤2^(smallBinaryLength r c) := by
    apply (show (∑ i,r i)+1 ≤ stateBound r c+1 by unfold stateBound; omega).trans
    exact (smallBinaryLength_parameters r c).2.2
  have hdim : Fintype.card I*Fintype.card J≤dimensionAllowance (I := I) (J := J) := by
    unfold dimensionAllowance
    nlinarith
  calc
    _ ≤ ((∑ i,r i)+1)^(Fintype.card I*Fintype.card J) := table_card_le r c
    _ ≤ (2^(smallBinaryLength r c))^(Fintype.card I*Fintype.card J) := Nat.pow_le_pow_left hn _
    _ = 2^(smallBinaryLength r c*(Fintype.card I*Fintype.card J)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)

lemma table_card_correction_bound (r : I → ℕ) (c : J → ℕ) :
    Fintype.card (Table r c)≤2^(correctionPrecision r c) := by
  apply (table_card_binary_bound r c).trans
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.mul_le_mul (Nat.le_self_pow (by decide : 6≠0) _)
    (Nat.le_self_pow (by decide : 2≠0) _)

lemma correction_card_mass (r : I → ℕ) (c : J → ℕ) :
    (Fintype.card (Table r c):ℚ)*(1/(2:ℚ)^(correctionPrecision r c))≤1 := by
  rw [mul_one_div]
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast table_card_correction_bound r c

end ContingencyTables.SmallGraphProfiles

end OAI
