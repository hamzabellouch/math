import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhysicalNormalizer

namespace OAI

/-! # The actual far-penalty terminal mass is exponentially small -/

namespace ContingencyTables.CompanionFarMass

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionPhysicalNormalizer TreeMarginalSignature
open BalancedCellFibres ForestPenaltyApplication

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def actualWeight (A : Instance I J) (alpha : ℝ) (a : Profiles (cellWidth A)) : ℝ :=
  physicalWeight A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
    (ForestLiteralCount.width A.T A.d A.b) A.r A.c alpha (BalancedCellFibres.profile (cellWidth A) a)

noncomputable def actualPenalty (A : Instance I J) (a : Profiles (cellWidth A)) : ℝ :=
  penalty A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
    (ForestLiteralCount.width A.T A.d A.b) A.r A.c (BalancedCellFibres.profile (cellWidth A) a)

lemma weight_at_large_penalty (A : Instance I J) (alpha : ℝ) (K : ℕ)
    (a : Profiles (cellWidth A)) (ha : 4*(K:ℝ) ≤ alpha*actualPenalty A a) :
    actualWeight A alpha a ≤ (2:ℝ)^(-(4*K:ℕ):ℝ) := by
  unfold actualWeight
  rw [exact_eq]
  split_ifs
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    change -alpha*actualPenalty A a ≤ -((4*K:ℕ):ℝ)
    push_cast
    linarith
  · exact (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).le

/-- The true expanded physical box has at most 2^K summands, so the
entire terminal region whose penalty is at least 4K contributes at most
2^(-3K). Neither a table-count approximation nor an oracle is assumed. -/
theorem far_mass_le (A : Instance I J) (alpha : ℝ) (B K : ℕ)
    (hW : 20*A.d ≤ A.W) (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K) :
    (∑ a : Profiles (cellWidth A),if 4*(K:ℝ) ≤ alpha*actualPenalty A a
      then actualWeight A alpha a else 0) ≤ (2:ℝ)^(-(3*K:ℕ):ℝ) := by
  have hcard : Fintype.card (Profiles (cellWidth A)) ≤ 2^K :=
    ForestBoxCardinality.cardinality_le_two_pow A hW B K hB hBK
  have hcardR : (Fintype.card (Profiles (cellWidth A)):ℝ) ≤ (2:ℝ)^K := by exact_mod_cast hcard
  have hp : 0 ≤ (2:ℝ)^(-(4*K:ℕ):ℝ) := (Real.rpow_pos_of_pos (by norm_num) _).le
  calc
    _ ≤ ∑ _a : Profiles (cellWidth A),(2:ℝ)^(-(4*K:ℕ):ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs with ha
      · exact weight_at_large_penalty A alpha K a ha
      · exact hp
    _ = (Fintype.card (Profiles (cellWidth A)):ℝ)*(2:ℝ)^(-(4*K:ℕ):ℝ) := by simp
    _ ≤ (2:ℝ)^K*(2:ℝ)^(-(4*K:ℕ):ℝ) := mul_le_mul_of_nonneg_right hcardR hp
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      push_cast
      ring

end ContingencyTables.CompanionFarMass

end OAI
