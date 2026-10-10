import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceHistory

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale
attribute [local instance] Classical.propDecidable

theorem norm_four_sum_le {I J H : Type*} [Fintype H]
    (R : Finset I) (A : Finset J) (F : I → J → H → H → ℂ) (ε : ℝ)
    (hF : ∀p∈R,∀e∈A,∀h h',‖F p e h h'‖≤ε) :
    ‖∑p∈R,∑e∈A,∑h,∑h',F p e h h'‖ ≤
      (R.card:ℝ)*(A.card:ℝ)*(Fintype.card H:ℝ)^2*ε := by
  have hh : ‖∑p∈R,∑e∈A,∑h,∑h',F p e h h'‖ ≤
      ∑p∈R,∑e∈A,∑h:H,∑h':H,ε := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro p hp
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro e he
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro h hm
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun h' _=>hF p hp e he h h')
  apply hh.trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k) (B V : (l:ℕ) → State k (l+1) → ℤ)

theorem sourceMatchingAverage_le_of_pair_norm
    (A : Finset (Equiv.Perm (ActualCopied w.configuration (wordSize k L) j)))
    {ε : ℝ} (hε : 0≤ε)
    (hpair : ∀P∈sourcePivotRanges w j,∀e∈A,
      ∀h h':SourceHistory (k:=k) (L:=L) (BD:=BD) j,
        ‖sourceHistoryPairMean w j hj B V P e h h'‖≤ε) :
    sourceMatchingAverage w j hj B V A ≤
      copiedNormalization (actualCopiedShells w.configuration (wordSize k L) j
        (s.locations.base 0) (s.locations.base 2) s.locations.primes)*
      Real.exp (-gapSchedule BD k L (j+1)+sourceAtomWidth k c)*
      (A.card:ℝ)*(Fintype.card (SourceHistory (k:=k) (L:=L) (BD:=BD) j):ℝ)^2*ε := by
  let C := copiedNormalization (actualCopiedShells w.configuration (wordSize k L) j
    (s.locations.base 0) (s.locations.base 2) s.locations.primes)
  let T := sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j
  let D := gapSchedule BD k L (j+1)
  let n := Fintype.card (SourceHistory (k:=k) (L:=L) (BD:=BD) j)
  have hC : 0≤C := copiedNormalization_nonneg _ (fun i=>sourceScheduledShells_pos w j _)
  have hnorm := norm_four_sum_le (sourcePivotRanges w j) A
    (sourceHistoryPairMean w j hj B V) ε hpair
  have hP : ((sourcePivotRanges w j).card:ℝ)≤Real.exp (T+sourceAtomWidth k c) :=
    pivotWindow_card_le _ _
  rw [sourceMatchingAverage_eq_normalized_history]
  calc
    _ ≤ C*Real.exp (-T-D)*‖∑P∈sourcePivotRanges w j,∑e∈A,
        ∑h:SourceHistory (k:=k) (L:=L) (BD:=BD) j,
        ∑h':SourceHistory (k:=k) (L:=L) (BD:=BD) j,sourceHistoryPairMean w j hj B V P e h h'‖ :=
      mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (mul_nonneg hC (Real.exp_pos _).le)
    _ ≤ C*Real.exp (-T-D)*(((sourcePivotRanges w j).card:ℝ)*(A.card:ℝ)*(n:ℝ)^2*ε) :=
      mul_le_mul_of_nonneg_left hnorm (mul_nonneg hC (Real.exp_pos _).le)
    _ ≤ C*Real.exp (-T-D)*(Real.exp (T+sourceAtomWidth k c)*(A.card:ℝ)*(n:ℝ)^2*ε) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Real.exp_pos _).le)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hP (Nat.cast_nonneg _)) (sq_nonneg _)) hε
    _ = _ := by
      change C*Real.exp (-T-D)*(Real.exp (T+sourceAtomWidth k c)*(A.card:ℝ)*(n:ℝ)^2*ε)=
        C*Real.exp (-D+sourceAtomWidth k c)*(A.card:ℝ)*(n:ℝ)^2*ε
      have he : Real.exp (-T-D)*Real.exp (T+sourceAtomWidth k c)=
          Real.exp (-D+sourceAtomWidth k c) := by rw [←Real.exp_add];congr 1;ring
      calc
        _ = C*(Real.exp (-T-D)*Real.exp (T+sourceAtomWidth k c))*(A.card:ℝ)*(n:ℝ)^2*ε := by ring
        _ = _ := by rw [he]

theorem sourceChangingAverage_le_of_pair_norm {ε : ℝ} (hε : 0≤ε)
    (hpair : ∀P∈sourcePivotRanges w j,
      ∀e∈Finset.univ\codePreservingMatchings w.configuration (wordSize k L) j,
      ∀h h':SourceHistory (k:=k) (L:=L) (BD:=BD) j,
        ‖sourceHistoryPairMean w j hj B V P e h h'‖≤ε) :
    sourceChangingAverage w j hj B V ≤
      copiedNormalization (actualCopiedShells w.configuration (wordSize k L) j
        (s.locations.base 0) (s.locations.base 2) s.locations.primes)*
      Real.exp (-gapSchedule BD k L (j+1)+sourceAtomWidth k c)*
      (Fintype.card (Equiv.Perm (ActualCopied w.configuration (wordSize k L) j)):ℝ)*
      (Fintype.card (SourceHistory (k:=k) (L:=L) (BD:=BD) j):ℝ)^2*ε := by
  apply (sourceMatchingAverage_le_of_pair_norm w j hj B V _ hε hpair).trans
  have hc : ((Finset.univ\codePreservingMatchings w.configuration (wordSize k L) j).card:ℝ) ≤
      Fintype.card (Equiv.Perm (ActualCopied w.configuration (wordSize k L) j)) := by
    exact_mod_cast Finset.card_le_univ _
  have hn := copiedNormalization_nonneg
    (actualCopiedShells w.configuration (wordSize k L) j
      (s.locations.base 0) (s.locations.base 2) s.locations.primes)
    (fun i=>sourceScheduledShells_pos w j _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc (mul_nonneg hn (Real.exp_pos _).le)) (sq_nonneg _)) hε

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
