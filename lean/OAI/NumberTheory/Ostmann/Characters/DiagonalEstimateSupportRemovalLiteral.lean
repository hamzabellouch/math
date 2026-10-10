import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template SymbolicHistory Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale HistoryFrequencyLabels HistoryFrequencyBudget
open TemplateOneSidedSupportSurviving TemplateOneSidedSupportTelescoping
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem cutoffSourceSurvivorKernel_eq_guarded_phase
    {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k) (B V : (l:ℕ) → State k (l+1) → ℤ) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) (hroot : h.val.1=h'.val.1)
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) → PrimeUpTo s.locations.Q) :
    cutoffSourceSurvivorKernel w j hj B V P e h h' x =
      copiedWindowRatio
        (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+gapSchedule BD k L (j+1))
        (sourceCopiedWidth k c) ((∏i,(x (.inl i)).val:ℕ):ℤ)*
      sourceSurvivorPairPhase w j hj P e h h' x *
      sourceRetainedWeight w j B V P (Equiv.refl _) h x *
      conj (sourceRetainedWeight w j B V P e h' x) := by
  have hsame : historyRootIndex j (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [] h'=
      historyRootIndex j (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [] h :=
    Subtype.ext hroot.symm
  by_cases hg : Pairwise (fun i v=>(x i).val.Coprime (x v).val) ∧
      pivotPrimeGuard (sourceWidth w.configuration (wordSize k L)) P x
  · simp only [sourceSurvivorPairPhase,ite_eq_left hg,cutoffSourceSurvivorKernel,ite_eq_left hsame,
      sourceCounterpartProduct,sourceCounterpartSample,sourceRetainedUnitPhase,sourceRetainedWeight,
      sourceHistoryTerm,unitHistoryTerm,RetainedRow.term,Equiv.refl_apply,Sum.elim_inl,Sum.elim_inr,map_mul]
    ring
  · have hz : sourceHistoryTerm w j hj B V (fun i=>x (.inr i)) P (fun i=>x (.inl i)) h=0 := by
      by_contra hn
      have hs := sourceHistoryTerm_surviving_support w j hj B V (fun i=>x (.inr i)) P
        (fun i=>x (.inl i)) h hn
      have he : Sum.elim (fun i=>x (.inl i)) (fun i=>x (.inr i))=x := by
        funext i
        cases i <;> rfl
      rw [he] at hs
      exact hg hs
    simp only [cutoffSourceSurvivorKernel,ite_eq_left hsame,hz,zero_mul,mul_zero,
      sourceSurvivorPairPhase,ite_eq_right hg]

end Ostmann.Characters.DiagonalEstimate

end

end OAI
