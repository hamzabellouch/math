import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodesShells
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceHistory

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale
attribute [local instance] Classical.propDecidable

theorem normalizedHistoryPair_eq_zero_of_unsupported_matching
    {I H K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K] {Q : ℕ}
    (E : I → Finset (PrimeUpTo Q)) (hE : ∀i,0 < primeShellMass (E i))
    (root : H → K) (F : (I → PrimeUpTo Q) → H → ℂ)
    (T D : ℝ) (e : Equiv.Perm I) (h h' : H)
    (hmatch : ∀f,(productPrior (fun i=>primeShellPrior (E i) (hE i))).mass f ≠ 0 →
      ¬∀i,f (e i)∈E i) :
    normalizedHistoryPair E hE root F T D e h h'=0 := by
  unfold normalizedHistoryPair FinitePrior.cmean
  apply Finset.sum_eq_zero
  intro f hf
  by_cases hm : (productPrior (fun i=>primeShellPrior (E i) (hE i))).mass f=0
  · simp only [hm,Complex.ofReal_zero,zero_mul]
  · have hp : (∏i,if f (e i)∈E i then (1:ℝ) else 0)=0 := by
      by_contra hn
      apply hmatch f hm
      intro i
      by_contra hi
      apply hn
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hi,ite_false])
    simp only [hp,mul_zero,Complex.ofReal_zero,zero_mul]

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k) (B V : (l:ℕ) → State k (l+1) → ℤ)

theorem sourceHistoryPairMean_eq_zero_of_root_ne
    (P : ℕ+) (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (hroot : historyRootIndex j
      (HistoryFrequencyBudget.ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [] h' ≠
      historyRootIndex j
      (HistoryFrequencyBudget.ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [] h) :
    sourceHistoryPairMean w j hj B V P e h h'=0 := by
  unfold sourceHistoryPairMean normalizedHistoryPair
  simp only [hroot,ite_false,mul_zero,FinitePrior.cmean,Finset.sum_const_zero]

theorem sourceHistoryPairMean_eq_zero_of_not_preserves_bulk
    (P : ℕ+) (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (he : ¬∀i,IsCopiedBulk w.configuration (wordSize k L) j (e i) ↔
      IsCopiedBulk w.configuration (wordSize k L) j i) :
    sourceHistoryPairMean w j hj B V P e h h'=0 := by
  have hw : 0 < s.locations.w := by
    linarith [s.locations.small_start,s.locations.small_end]
  have hsource : (fun i=>sourceScheduledShells w j
      (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) i)) =
      actualCopiedShells w.configuration (wordSize k L) j
        (s.locations.base 0) (s.locations.base 2) s.locations.primes := rfl
  unfold sourceHistoryPairMean FinitePrior.cmean
  apply Finset.sum_eq_zero
  intro y hy
  apply mul_eq_zero_of_right
  apply normalizedHistoryPair_eq_zero_of_unsupported_matching
  intro f hf hs
  apply he
  intro i
  have hfi := primeProductPrior_mem_of_mass_ne_zero _
    (fun _=>sourceScheduledShells_pos w j _) f hf (e i)
  have hsi := hs i
  have hfis := (congrArg (fun A=>f (e i)∈A) (congrFun hsource (e i))).mp hfi
  have hsis := (congrArg (fun A=>f (e i)∈A) (congrFun hsource i)).mp hsi
  exact (actualCopied_mem_bulk_iff w hw j (e i) (f (e i)) hfis).symm.trans
    (actualCopied_mem_bulk_iff w hw j i (f (e i)) hsis)

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
