import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhysicalNormalizer

namespace OAI

/-! # Exponential far-penalty bound for the actual selected-root mass -/

namespace ContingencyTables.RootedFarMass

open scoped BigOperators Classical
open CompanionFactorialApplication TreeMarginalSignature BalancedCellFibres

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def actualWeight (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (a : Profiles (cellWidth A)) : ℝ :=
  RootedPenalty.physicalWeight A R alpha (BalancedCellFibres.profile (cellWidth A) a)

noncomputable def actualPenalty (A : Instance I J) (R : RootedCompletion.Selection A.T) (a : Profiles (cellWidth A)) : ℝ :=
  RootedPenalty.penalty A R (BalancedCellFibres.profile (cellWidth A) a)

lemma weight_at_large_penalty (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (K : ℕ)
    (a : Profiles (cellWidth A)) (ha : 4*(K:ℝ) ≤ alpha*actualPenalty A R a) :
    actualWeight A R alpha a ≤ (2:ℝ)^(-(4*K:ℕ):ℝ) := by
  unfold actualWeight
  rw [RootedPenalty.exact_eq]
  split_ifs
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    change -alpha*actualPenalty A R a ≤ -((4*K:ℕ):ℝ)
    push_cast
    linarith
  · exact (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).le

/-- The true expanded physical box has at most 2^K summands, so the
entire terminal region whose penalty is at least 4K contributes at most
2^(-3K). Neither a table-count approximation nor an oracle is assumed. -/
theorem far_mass_le (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (B K : ℕ)
    (hW : 20*A.d ≤ A.W) (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K) :
    (∑ a : Profiles (cellWidth A),if 4*(K:ℝ) ≤ alpha*actualPenalty A R a
      then actualWeight A R alpha a else 0) ≤ (2:ℝ)^(-(3*K:ℕ):ℝ) := by
  have hcard : Fintype.card (Profiles (cellWidth A)) ≤ 2^K :=
    ForestBoxCardinality.cardinality_le_two_pow A hW B K hB hBK
  have hcardR : (Fintype.card (Profiles (cellWidth A)):ℝ) ≤ (2:ℝ)^K := by exact_mod_cast hcard
  have hp : 0 ≤ (2:ℝ)^(-(4*K:ℕ):ℝ) := (Real.rpow_pos_of_pos (by norm_num) _).le
  calc
    _ ≤ ∑ _a : Profiles (cellWidth A),(2:ℝ)^(-(4*K:ℕ):ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs with ha
      · exact weight_at_large_penalty A R alpha K a ha
      · exact hp
    _ = (Fintype.card (Profiles (cellWidth A)):ℝ)*(2:ℝ)^(-(4*K:ℕ):ℝ) := by simp
    _ ≤ (2:ℝ)^K*(2:ℝ)^(-(4*K:ℕ):ℝ) := mul_le_mul_of_nonneg_right hcardR hp
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      push_cast
      ring

end ContingencyTables.RootedFarMass

end OAI
