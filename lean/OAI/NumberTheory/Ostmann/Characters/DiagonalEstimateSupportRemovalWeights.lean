import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurvivingFamilies
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingPairLiteral

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template SymbolicHistory Preliminaries TemplateOneSidedSupportSurviving
open TemplateOneSidedSupportTelescoping TemplateOneSidedRelabel
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem matched_surviving_pair_support {k j Q : ℕ} (hj : j<k)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (s : Bool → ℤ) (P : ℕ+) (width : Role → ℕ)
    (p : SurvivingPrimeIndex k j width → PrimeUpTo Q)
    (e : Bool → Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (t : Bool → HistoryReconstruction.Tree j)
    (hpairs : Pairwise (fun i v=>(p i).val.Coprime (p v).val)) :
    (∀r,TransferSupport k B V extra j (s r)
      (evalExpressions (groupedPrimeAssignment width p) (groupedExpressions k j width P (e r))) (t r)) ↔
    pivotPrimeGuard width P p ∧ ∀r,
      SampledTransferSupport k
        (fun u=>∏a,groupedPrimeAssignment width p (groupedPermutation k j width (e r) ⟨u,a⟩))
        B V extra j (origins k j) (s r)
        (evalExpressions (groupedPrimeAssignment width p) (groupedExpressions k j width P (e r))) (t r) := by
  simp_rw [matched_transferSupport_iff_guarded_sampled hj B V extra _ P width p _ _ hpairs]
  constructor
  · intro h
    exact ⟨(h false).1,fun r=>(h r).2⟩
  · rintro ⟨hp,h⟩ r
    exact ⟨hp,h r⟩

theorem matched_surviving_retained_pair_eq_sampled {k j Q : ℕ} (hj : j<k)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W T Wc : ℝ)
    (s : Bool → ℤ) (P : ℕ+) (width : Role → ℕ)
    (p : SurvivingPrimeIndex k j width → PrimeUpTo Q)
    (e : Bool → Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (t : Bool → HistoryReconstruction.Tree j)
    (prod : ((Σi:SurvivingSlot k j,Fin (survivingWidth k j width i)) → ℤ) → ℤ)
    (phase : ((Σi:SurvivingSlot k j,Fin (survivingWidth k j width i)) → ℤ) → ℂ)
    (hpairs : Pairwise (fun i v=>(p i).val.Coprime (p v).val)) :
    let a := groupedPrimeAssignment width p
    let x := fun r x=>evalExpressions x (groupedExpressions k j width P (e r))
    copiedWindowRatio T Wc (prod a)*phase a*
      retainedHistoryWeight k B V extra mask X Δ W j (s false) (x false a) (t false)*
      conj (retainedHistoryWeight k B V extra mask X Δ W j (s true) (x true a) (t true)) =
    if pivotPrimeGuard width P p ∧ ∀r,
      SampledTransferSupport k (fun u=>∏b,a (groupedPermutation k j width (e r) ⟨u,b⟩))
        B V extra j (origins k j) (s r) (x r a) (t r)
    then pairedHistoryMultiplier k mask X Δ W T Wc j s x t prod phase a else 0 := by
  dsimp only
  rw [retained_pair_eq_indicator k B V extra mask X Δ W T Wc j s
    (fun r x=>evalExpressions x (groupedExpressions k j width P (e r))) t prod phase
    (groupedPrimeAssignment width p)]
  simp only [matched_surviving_pair_support hj B V extra s P width p e t hpairs]

end Ostmann.Characters.DiagonalEstimate

end

end OAI
