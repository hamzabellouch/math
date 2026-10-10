import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseFinishProgram

namespace OAI

/-! # Additive binary-size bounds for stored phase arithmetic -/
namespace ContingencyTables.CompanionFractionSize
open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionMultiplierProgram CompanionPhaseCounts

lemma height_mul (a b : TreeFraction.Fraction) :
    TreeFraction.height (TreeFraction.mul (a,b)) ≤ TreeFraction.height a+TreeFraction.height b+1 := by
  have hn := TreeFraction.normalize_size_num (a.1*b.1,a.2*b.2)
  have hd := TreeFraction.normalize_size_den (a.1*b.1,a.2*b.2)
  have hnum := nat_size_mul a.1 b.1
  have hden := nat_size_mul a.2 b.2
  have ha := le_max_left a.1.size a.2.size
  have ha' := le_max_right a.1.size a.2.size
  have hb := le_max_left b.1.size b.2.size
  have hb' := le_max_right b.1.size b.2.size
  dsimp only at hn hd
  change (TreeFraction.mul (a,b)).1.size ≤ _ at hn
  change (TreeFraction.mul (a,b)).2.size ≤ _ at hd
  unfold TreeFraction.height
  apply max_le <;> omega

lemma height_div (a b : TreeFraction.Fraction) :
    TreeFraction.height (TreeFraction.div (a,b)) ≤ TreeFraction.height a+TreeFraction.height b+1 := by
  have hn := TreeFraction.normalize_size_num (a.1*b.2,a.2*b.1)
  have hd := TreeFraction.normalize_size_den (a.1*b.2,a.2*b.1)
  have hnum := nat_size_mul a.1 b.2
  have hden := nat_size_mul a.2 b.1
  have ha := le_max_left a.1.size a.2.size
  have ha' := le_max_right a.1.size a.2.size
  have hb := le_max_left b.1.size b.2.size
  have hb' := le_max_right b.1.size b.2.size
  dsimp only at hn hd
  change (TreeFraction.div (a,b)).1.size ≤ _ at hn
  change (TreeFraction.div (a,b)).2.size ≤ _ at hd
  unfold TreeFraction.height
  apply max_le <;> omega

lemma countRatio_height (z : DefectCountInput) : TreeFraction.height (countRatio z) ≤ z.1.2.length := by
  have hp : plainCountCode z.1 ≤ z.1.2.length := List.length_filter_le _ _
  have hd : defectCountCode z ≤ z.1.2.length := List.length_filter_le _ _
  have hs (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  exact max_le ((hs _).trans hp) ((hs _).trans hd)

lemma updateCode_height (z : UpdateInput) :
    TreeFraction.height (updateCode z) ≤ TreeFraction.height z.2+z.1.1.2.length+1 := by
  unfold updateCode
  split_ifs
  · omega
  · exact (height_mul _ _).trans (Nat.add_le_add_right
      (Nat.add_le_add_left (countRatio_height _) _) 1)

lemma sum_height (xs : List TreeFraction.Fraction) (M : ℕ)
    (hm : ∀ x∈xs,TreeFraction.height x ≤ M) :
    TreeFraction.height (TreeFraction.sum xs) ≤ 1+xs.length*(M+2) := by
  simpa only [TreeFraction.sum,TreeFraction.height,Nat.size_zero,Nat.size_one,Nat.zero_max] using
    TreeFraction.fractionFold_height xs (0,1) M hm

lemma term_height (z : CompanionPhaseFinishProgram.TermInput) (M : ℕ)
    (h₁ : TreeFraction.height z.2.1 ≤ M) (h₂ : TreeFraction.height z.2.2 ≤ M) :
    TreeFraction.height (CompanionPhaseFinishProgram.term z) ≤ 2*M+1 := by
  unfold CompanionPhaseFinishProgram.term
  split_ifs
  · have h := height_div z.2.2 z.2.1
    omega
  · norm_num [TreeFraction.height]

end ContingencyTables.CompanionFractionSize

end OAI
