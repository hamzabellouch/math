import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperStationaryMass
import OAI.Combinatorics.ContingencyTables.Transport.BalancedCompletionMass
import OAI.Combinatorics.ContingencyTables.Parameters

namespace OAI

/-! # The stationary successful-pair ratio of the first sampler -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open FirstPaperPhysicalMarginal PhysicalCompletionFibres PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def paperLarge (r : I → ℕ) (c : J → ℕ) : Finset (I×J) :=
  Finset.univ.filter (fun p => paperSmall r c p.1 p.2=false)

lemma large_padding_rows (small : I → J → Bool) (r : I → ℕ) (L : ℕ) :
    paddedRows r (largePadding (Finset.univ.filter (fun p : I×J => small p.1 p.2=false)) L)=
      (fun i => r i+rowLargeCount small i*L) := by
  funext i
  unfold paddedRows rowLargeCount
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  cases hs : small i j <;> simp [largePadding,hs]

lemma large_padding_columns (small : I → J → Bool) (c : J → ℕ) (L : ℕ) :
    paddedColumns c (largePadding (Finset.univ.filter (fun p : I×J => small p.1 p.2=false)) L)=
      (fun j => c j+columnLargeCount small j*L) := by
  funext j
  unfold paddedColumns columnLargeCount
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hs : small i j <;> simp [largePadding,hs]


lemma paper_padded_count_le (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i,r i=∑ j,c j) (hd : 14 ≤ dimensionAllowance (I := I) (J := J)) :
    (Fintype.card (Table
      (fun i => r i+rowLargeCount (paperSmall r c) i*((dimensionAllowance (I := I) (J := J))^12))
      (fun j => c j+columnLargeCount (paperSmall r c) j*((dimensionAllowance (I := I) (J := J))^12))):ℝ) ≤
      2*(Fintype.card (Table r c):ℝ) := by
  let d := dimensionAllowance (I := I) (J := J)
  let K := paperLarge r c
  have hK : K.card ≤ d :=
    (Finset.card_filter_le _ _).trans (by simpa only [Finset.card_univ,Fintype.card_prod] using
      (dimension_le_allowance (I := I) (J := J)))
  have hrow : ∀ p ∈ K,d^20 ≤ r p.1 := by
    intro p hp
    exact ((firstPaperSmall_false_iff r c _ _ _).mp (Finset.mem_filter.mp hp).2).1
  have hcol : ∀ p ∈ K,d^20 ≤ c p.2 := by
    intro p hp
    exact ((firstPaperSmall_false_iff r c _ _ _).mp (Finset.mem_filter.mp hp).2).2
  have hr : Fintype.card I ≤ d := by dsimp only [d]; unfold dimensionAllowance; nlinarith
  have hc : Fintype.card J ≤ d := by dsimp only [d]; unfold dimensionAllowance; nlinarith
  have h := padding_success_half r c htotal K d hd hr hc hK hrow hcol
  have htotal' : ∑ i,paddedRows r (largePadding K (d^12)) i=
      ∑ j,paddedColumns c (largePadding K (d^12)) j := by
    unfold paddedRows paddedColumns
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,htotal,Finset.sum_comm]
  have hpos : (0:ℝ) < Fintype.card
      (Table (paddedRows r (largePadding K (d^12))) (paddedColumns c (largePadding K (d^12)))) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (table_nonempty _ _ htotal')
  have hh := (le_div_iff₀ hpos).mp h
  simp only [Fintype.card_eq_nat_card] at hh ⊢
  dsimp only [K,paperLarge] at hh
  rw [large_padding_rows,large_padding_columns] at hh
  change (Nat.card (Table (fun i => r i+rowLargeCount (paperSmall r c) i*d^12)
    (fun j => c j+columnLargeCount (paperSmall r c) j*d^12)):ℝ) ≤ 2*Nat.card (Table r c)
  linarith

/-- The numerator counts original tables through the padding bijection;
the denominator counts all actual small-state/completion pairs. -/
theorem state_mass_le_original_count (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i,r i=∑ j,c j) (hd : 14 ≤ dimensionAllowance (I := I) (J := J)) :
    (∑ z,stateWeight r c z) ≤
      2*(1+(dimensionAllowance (I := I) (J := J):ℝ)^2)*(Fintype.card (Table r c):ℝ) := by
  have h₁ := state_mass_le_balanced r c
  have h₂ := word_mass_le_padded_count (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20)
    (stateCapacity_small r c)
  have h₃ := paper_padded_count_le r c htotal hd
  have h := h₁.trans (mul_le_mul_of_nonneg_left (h₂.trans h₃) (by positivity))
  convert h using 1
  ring

theorem stationary_success_ratio (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (htotal : ∑ i,r i=∑ j,c j) (hd : 14 ≤ dimensionAllowance (I := I) (J := J)) :
    1/(2*(1+(dimensionAllowance (I := I) (J := J):ℝ)^2)) ≤
      (Fintype.card (Table r c):ℝ)/(∑ z,stateWeight r c z) := by
  have hm : 0 < ∑ z,stateWeight r c z :=
    Finset.sum_pos (fun z _ => stateWeight_positive r c z) Finset.univ_nonempty
  apply (div_le_div_iff₀ (by positivity) hm).mpr
  simpa only [one_mul,mul_comm] using state_mass_le_original_count r c htotal hd

end ContingencyTables.SmallGraphProfiles

end OAI
