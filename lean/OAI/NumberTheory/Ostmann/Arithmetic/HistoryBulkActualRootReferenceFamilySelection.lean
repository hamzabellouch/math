import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyWitness

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

def selectWitness (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) :
    Option (Witness C outside σ a x y J w P Q i) := by
  classical
  exact if hn : wholeMean C outside σ a x y J w P Q i = 0 then none else
    some (Classical.choice (witness_nonempty C outside σ a x y J w P Q
      hactual hl ha hc he houtside hw hpos i hn))

theorem selectWitness_none_iff (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) :
    selectWitness C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos i = none ↔
      wholeMean C outside σ a x y J w P Q i = 0 := by
  classical
  unfold selectWitness
  split_ifs <;> simp_all

theorem selectWitness_isSome_iff (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) :
    (selectWitness C outside σ a x y J w P Q hactual hl ha hc he houtside hw hpos i).isSome ↔
      wholeMean C outside σ a x y J w P Q i ≠ 0 := by
  classical
  unfold selectWitness
  split_ifs <;> simp_all

end Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamily

end

end OAI
