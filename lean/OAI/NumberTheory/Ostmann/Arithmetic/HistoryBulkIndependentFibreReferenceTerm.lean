import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceSelection
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTermOrdered
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingActual

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentFibreReference
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryGiantReferenceMean
open HistoryGiantOriginalMeanFactorization (Current Choices)
open HistoryDiagonalRemainingRootMatching HistoryBulkIndependentReferenceFrequency
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (a : SelectedNonbulkSample C l) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
variable (he : PreservesRemainingBands _ e) (s t : ℤ) (c₁ c₂ : Choices (l:=l) C)

def bulkPermutation :=
  inducedBulkPermutation (2*(bulkSize k L/2)) k l (fullPermutation (l+1) _ e he)
    (fullPermutation_bulk (l+1) _ e he)

def referenceTerm (K : ℕ) (r : Reference C outside a e s t c₁ c₂)
    (u : SelectedBulkSample C l) (hc : Compatible C a e u) (P Q : ℤ) : ℂ :=
  HistoryBulkIndependentReferenceTerm.orderedReferenceTerm C (frequencyBound Bs BD Bz k L)
    outside l K (bulkPermutation e he)
    (fibreAssignment C a r.bulk) (rightAssignment C a e r.bulk r.compatible)
    (fibreAssignment C a u) (rightAssignment C a e u hc) s t
    (mixedP C.giantCenter C.giant r.draw).toNat (mixedQ C.giantCenter C.giant r.draw).toNat c₁ c₂
    r.supported.1 r.supported.2 (bulkSize k L/2) (bulkSize k L/2)
    C.scale C.bulkBin C.spectatorBin C.giantCenter (multiplier C outside a e s u hc) P Q

theorem compatibleTerm_eq_referenceTerm
    {spectator : PrimeSource}
    (hactual : HistoryBulkIndependentReferenceTerm.SelectedOrderedReferenceEquality C spectator)
    (K : ℕ) (hle : l≤K) (hl : l≤k)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc₁ : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c₁≠0)
    (hc₂ : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c₂≠0)
    (houtside : ∀q∈outside,∃p : spectator.Sample,(p:ℕ)=q)
    (r : Reference C outside a e s t c₁ c₂) (u : SelectedBulkSample C l)
    (hc : Compatible C a e u) (hu : (selectedBulkPrior C l).mass u≠0)
    (hy : (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).mass
      (rightAssignment C a e u hc)≠0)
    (P Q : ℤ) (hp : 0<P) (hq : 0<Q) :
    compatibleTerm C outside a e s t c₁ c₂ u hc P Q=
      referenceTerm C outside a e he s t c₁ c₂ K r u hc P Q := by
  exact hactual outside l K hle hl
    (fibreAssignment C a r.bulk) (rightAssignment C a e r.bulk r.compatible)
    (fibreAssignment C a u) (rightAssignment C a e u hc) s t
    (mixedP C.giantCenter C.giant r.draw).toNat (mixedQ C.giantCenter C.giant r.draw).toNat c₁ c₂
    r.supported.1 r.supported.2 (bulkSize k L/2) (bulkSize k L/2)
    C.scale C.bulkBin C.spectatorBin C.giantCenter (multiplier C outside a e s u hc) P Q
    (fullPermutation (l+1) _ e he) (fullPermutation_bulk (l+1) _ e he)
    (counterpartCurrentAssignment_value C _ e he r.compatible)
    (counterpartCurrentAssignment_value C _ e he hc)
    (fibreAssignment_nonbulk_fixed C a u r.bulk)
    (counterpartCurrentAssignment_nonbulk_fixed C _ _ e he r.compatible hc
      (fibreAssignment_nonbulk_fixed C a u r.bulk))
    r.right_mass hy (ne_of_gt (fibreAssignment_mass_pos C a r.bulk ha r.bulk_pos))
    (ne_of_gt (fibreAssignment_mass_pos C a u ha
      (lt_of_le_of_ne ((selectedBulkPrior C l).mass_nonneg u) (Ne.symm hu))))
    hc₁ hc₂ hp hq houtside

end Ostmann.Arithmetic.HistoryBulkIndependentFibreReference

end

end OAI
