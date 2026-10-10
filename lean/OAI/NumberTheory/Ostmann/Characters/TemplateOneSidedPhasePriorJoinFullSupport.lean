import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportPrimes
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateUnitHistory
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoin

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries DiagonalEstimate
attribute [local instance] Classical.propDecidable

theorem survivingSample_pairwise_of_current {k j A : ℕ} (width : Role→ℕ)
    (h : CopiedConstituent (schedule k j) j width→PrimeUpTo A)
    (y : OutsideConstituent (schedule k j) j width→PrimeUpTo A) (P s : ℤ)
    (hs : CurrentAtomSupport k j s (sourceState k j P
      (copiedSampleState (schedule k j) j width h) (outsideSampleState (schedule k j) j width y)))
    (hh : copiedWithinAtomPrimeSupport (schedule k j) j width h)
    (hy : outsideWithinAtomPrimeSupport (schedule k j) j width y) :
    Pairwise (fun i v=>(Sum.elim h y i).val.Coprime (Sum.elim h y v).val) := by
  have hc : Pairwise (fun i v=>(h i).val.Coprime (h v).val) := by
    apply (pairwise_coprime_sigma_iff (fun i=>(h i).val)).mpr
    refine ⟨?_,hh⟩
    simpa only [copiedSampleState,←Nat.cast_prod,Nat.isCoprime_iff_coprime] using hs.copied_pairwise
  have ho : Pairwise (fun i v=>(y i).val.Coprime (y v).val) := by
    apply (pairwise_coprime_sigma_iff (fun i=>(y i).val)).mpr
    refine ⟨?_,hy⟩
    simpa only [outsideSampleState,←Nat.cast_prod,Nat.isCoprime_iff_coprime] using hs.outside_pairwise
  have hx (i : CopiedConstituent (schedule k j) j width)
      (v : OutsideConstituent (schedule k j) j width) : (h i).val.Coprime (y v).val := by
    have hp : (∏a,(h ⟨i.1,a⟩).val).Coprime (∏b,(y ⟨v.1,b⟩).val) := by
      simpa only [copiedSampleState,outsideSampleState,←Nat.cast_prod,Nat.isCoprime_iff_coprime]
        using hs.copied_outside_coprime i.1 v.1
    exact Nat.coprime_prod_right_iff.mp
      (Nat.coprime_prod_left_iff.mp hp i.2 (Finset.mem_univ _)) v.2 (Finset.mem_univ _)
  intro i v hiv
  cases i with
  | inl i =>
    cases v with
    | inl v => exact hc (fun he=>hiv (congrArg Sum.inl he))
    | inr v => exact hx i v
  | inr i =>
    cases v with
    | inl v => exact (hx v i).symm
    | inr v => exact ho (fun he=>hiv (congrArg Sum.inr he))

theorem unitHistoryTerm_surviving_pairwise (k j : ℕ) (hj : j<k) (width : Role→ℕ) {A : ℕ}
    (ζ : PrimeUnitData (schedule k j) width A) (χ : PrimeCharacterData (schedule k j) width A)
    (a : PrimeTranslationData (schedule k j) width A)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask : (l:ℕ)→ℤ→State k l→Prop) (X Δ W : ℝ)
    (ranges : List Bool→Finset ℤ) (path : List Bool)
    (y : OutsideConstituent (schedule k j) j width→PrimeUpTo A) (P : ℕ+)
    (f : CopiedConstituent (schedule k j) j width→PrimeUpTo A)
    (h : HistoryFrequencyLabels.SupportedHistory ranges j path)
    (hh : unitHistoryTerm k j hj width ζ χ a B V extra mask X Δ W ranges path y P f h≠0) :
    Pairwise (fun i v=>(Sum.elim f y i).val.Coprime (Sum.elim f y v).val) := by
  have hu : unitRetainedPhase k j hj width ζ χ a f y P h.val.1 h.val.2≠0 :=
    (mul_ne_zero_iff.mp hh).2
  have hp : sampledRetainedPhase k j hj width χ a f y P h.val.1 h.val.2≠0 :=
    (mul_ne_zero_iff.mp hu).2
  have hi : copiedWithinAtomPrimeSupport (schedule k j) j width f ∧
      outsideWithinAtomPrimeSupport (schedule k j) j width y := by
    by_contra hn
    exact hp (by simp only [sampledRetainedPhase,ite_eq_right hn])
  exact survivingSample_pairwise_of_current width f y P h.val.1
    (RetainedRow.term_current_support k j B V extra mask X Δ W P _ _ h.val _ hh) hi.1 hi.2

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
