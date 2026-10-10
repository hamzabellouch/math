import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterEquivBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageNormalize
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageOption
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageTerm

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkActualPrincipalBlockFamily HistoryBulkPrincipalKernelReplacementMatched
open HistoryBulkReferencePeriodicMeanSource HistoryBulkFibreOriginalReference
attribute [local instance] Classical.propDecidable
local instance kernelStageMeanBasicInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (outside : List ℕ) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p →
    Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
  (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
    |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hlen : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
  (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)

private theorem option_elim_mul {β : Type*} (r : Option β) (c : ℂ) (F : β → ℂ) :
    r.elim 0 (fun b=>c*F b)=c*r.elim 0 F := by
  cases r <;> simp only [Option.elim_none,Option.elim_some,mul_zero]

theorem densityPrincipalProductTerm_eq_jacobian_option
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (symbolic corrected mixed : Bool) (u : SelectedBulkSample C l)
    (ho : outerMass C l p o≠0) (hu : (selectedBulkPrior C l).mass u≠0) :
    densityPrincipalProductTerm (C:=C) (l:=l) symbolic
      (matchedPrincipalFamily C p outside σ J w P Q hactual hl houtside hw hpos hcell
        (bulkSize k L/2) hlen hprime hV true v f g)
      (selectedKernelDensitySources C p outside σ J w P Q hactual hl houtside hw hpos hcell
        hlen hprime hV v f g)
      corrected mixed
      (selectedKernelMask C p outside σ J w P Q hactual hl houtside hw hpos hcell hprime v f g)
      (restoreOriginalDraw C l p o u) =
    (∏q : Block p,((outerBlocks C l p o q).val:ℂ))*
      selectedKernelOptionValue C p outside σ J w P Q hactual hl houtside hw hpos hcell
        hlen hprime hV v f g o symbolic corrected mixed u := by
  rw [densityPrincipalProductTerm_eq_restoredOption (l:=l) C p outside σ J w P Q
    hactual hl houtside hw hpos hcell hlen hprime hV v f g o symbolic corrected mixed u]
  unfold selectedKernelOptionValue
  trans (selectMatchedOuterReference C p o outside σ (J o) w P Q (v,f,g)
      hactual hl houtside hw hpos).elim 0 (fun R=>
        (∏q : Block p,((outerBlocks C l p o q).val:ℂ))*
          R.kernelTerm (l:=l) hcell hlen hprime hV symbolic corrected mixed u)
  · apply congrArg (fun F=>(selectMatchedOuterReference C p o outside σ (J o) w P Q (v,f,g)
      hactual hl houtside hw hpos).elim 0 F)
    funext R
    exact R.restoredKernelTerm_eq_jacobian_mul (l:=l) hcell hlen hprime hV symbolic corrected mixed u
      (by rw [originalDrawMass_restore]; exact mul_ne_zero ho hu)
  · exact option_elim_mul _ _ _

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
