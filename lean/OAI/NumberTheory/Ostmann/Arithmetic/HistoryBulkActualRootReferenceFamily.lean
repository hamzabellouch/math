import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilySelection

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamily
open Construction Conclusion HistoryBulkSourceDisintegration HistoryGiantReferenceMean
open HistoryBulkFibreOriginalReference HistoryBulkReferenceFrequencyFamily
open HistoryBulkSelectedUniversalOperator HistorySignedXiTransport
open HistoryGiantOriginalMeanFactorization (Choices history)
open HistoryBulkFibreReference (originalMean)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

variable (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
variable (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
variable {α : Type} [Fintype α] (w : α → ℝ) (P Q : α → ℤ)

variable {spectator : PrimeSource}
variable (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l ≤ k) (ha : 0 < (selectedNonbulkPrior C l).mass a)
  (hc : ∀ i, choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l (leftChoices C x i) ≠ 0)
  (he : ∀ i, choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l (rightChoices C y i) ≠ 0)
  (houtside : ∀ q∈outside, ∃ p : spectator.Sample, (p:ℕ)=q)
  (hw : ∀ r, 0 ≤ w r) (hpos : ∀ r, w r ≠ 0 → 0 < P r ∧ 0 < Q r)

def referenceFamily : RootReferenceFamily C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) outside l x y :=
  fun i => (selectWitness C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos i).map
    (fun r => r.toReference)

def presentWitness (i : RootPresent (referenceFamily C outside σ a x y J w P Q
    hactual hl ha hc he houtside hw hpos)) : Witness C outside σ a x y J w P Q i.val :=
  (selectWitness C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos i.val).get
    (by simpa only [referenceFamily,Option.isSome_map] using i.property)

theorem rootSelected_eq_presentWitness
    (i : RootPresent (referenceFamily C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos)) :
    rootSelected (referenceFamily C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos) i =
      (presentWitness C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos i).toReference := by
  simp only [rootSelected,referenceFamily,presentWitness,Option.get_map]

theorem referenceFamily_none_iff
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) :
    referenceFamily C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos i = none ↔
      wholeMean C outside σ a x y J w P Q i = 0 := by
  simpa only [referenceFamily,Option.map_eq_none_iff] using
    selectWitness_none_iff C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos i

def actualData
    (hcell : ∀ v, w v ≠ 0 → 0 < P v ∧ 0 < Q v ∧
      |Real.log (P v:ℝ)-(C.giantCenter:ℝ)| ≤ 1 ∧
      |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)| ≤ 1)
    (i : RootPresent (referenceFamily C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos)) :
    ActualReferenceData C σ i.val
      (rootSelected (referenceFamily C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos) i) := by
  rw [rootSelected_eq_presentWitness]
  exact Witness.toActualData C outside σ a x y J w P Q
    (presentWitness C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos i) ha (hc i.val) (he i.val) hcell

theorem wholeMean_eq_selectedReferenceMean
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) :
    wholeMean C outside σ a x y J w P Q i =
      (selectWitness C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos i).elim 0
        (fun r => originalMean (selectedBulkPrior C l).mass w (fun u z =>
          weightedFibreReferenceTerm C outside σ a i.1.val i.1.val
            (leftChoices C x i) (rightChoices C y i) (J i) k r.bulk (P r.giant) (Q r.giant)
            r.supported u (P z) (Q z))) := by
  cases hs : selectWitness C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos i with
  | none =>
    simpa only [hs,Option.elim_none] using
      (selectWitness_none_iff C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos i).mp hs
  | some r =>
    simpa only [hs,Option.elim_some] using r.mean_eq

end Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamily

end

end OAI
