import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceWeighted
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperatorActualData

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
abbrev Index := RootFrequencyIndex (frequencyBound Bs BD Bz k L) l
abbrev Draws := InternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l

variable (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
variable (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
variable {α : Type} [Fintype α] (w : α → ℝ) (P Q : α → ℤ)

def leftChoices (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) : Choices (l:=l) C :=
  assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) l i.2.1 x

def rightChoices (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) : Choices (l:=l) C :=
  assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) l i.2.2 y

def wholeMean (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) : ℂ :=
  originalMean (selectedBulkPrior C l).mass w (fun u r =>
    weightedFibreTerm C outside σ a i.1.val i.1.val
      (leftChoices C x i) (rightChoices C y i) (J i) u (P r) (Q r))

structure Witness (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) where
  bulk : SelectedBulkSample C l
  giant : α
  bulk_pos : 0 < (selectedBulkPrior C l).mass bulk
  giant_pos : 0 < w giant
  term_ne : weightedFibreTerm C outside σ a i.1.val i.1.val
    (leftChoices C x i) (rightChoices C y i) (J i) bulk (P giant) (Q giant) ≠ 0
  supported : FibreSupported C outside σ a i.1.val i.1.val
    (leftChoices C x i) (rightChoices C y i) bulk (P giant) (Q giant)
  equality : ∀ u r, (selectedBulkPrior C l).mass u ≠ 0 → w r ≠ 0 →
    weightedFibreTerm C outside σ a i.1.val i.1.val
      (leftChoices C x i) (rightChoices C y i) (J i) u (P r) (Q r) =
    weightedFibreReferenceTerm C outside σ a i.1.val i.1.val
      (leftChoices C x i) (rightChoices C y i) (J i) k bulk (P giant) (Q giant) supported u (P r) (Q r)
  mean_eq : wholeMean C outside σ a x y J w P Q i =
    originalMean (selectedBulkPrior C l).mass w (fun u r =>
      weightedFibreReferenceTerm C outside σ a i.1.val i.1.val
        (leftChoices C x i) (rightChoices C y i) (J i) k bulk (P giant) (Q giant) supported u (P r) (Q r))

theorem witness_nonempty {spectator : PrimeSource}
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (hl : l ≤ k) (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : ∀ i, choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l (leftChoices C x i) ≠ 0)
    (he : ∀ i, choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l (rightChoices C y i) ≠ 0)
    (houtside : ∀ q∈outside, ∃ p : spectator.Sample, (p:ℕ)=q)
    (hw : ∀ r, 0 ≤ w r) (hpos : ∀ r, w r ≠ 0 → 0 < P r ∧ 0 < Q r)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
    (hn : wholeMean C outside σ a x y J w P Q i ≠ 0) :
    Nonempty (Witness C outside σ a x y J w P Q i) := by
  have hs := weightedWholeFibreMean_fixed_reference C outside σ a i.1.val i.1.val
    (leftChoices C x i) (rightChoices C y i) (J i) hactual k hl hl ha (hc i) (he i)
    houtside w P Q hw hpos
  rcases hs with hz | ⟨u,r,hu,hr,ht,hs,hall,hmean⟩
  · exact False.elim (hn hz)
  · exact ⟨⟨u,r,hu,hr,ht,hs,hall,hmean⟩⟩

end Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamily

end

end OAI
