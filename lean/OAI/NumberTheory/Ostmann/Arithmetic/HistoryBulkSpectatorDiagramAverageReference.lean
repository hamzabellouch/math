import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverageLeaf
import OAI.NumberTheory.Ostmann.Arithmetic.PermutationHaarConvention

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverage
open Construction HistoryResidueRegular HistorySignedSpectatorDiagram
open CanonicalHistoryLeafBulk PermutationDiagramComparison ResidueHaar
variable {q l m : ℕ} [Fact q.Prime] {V : ℕ→ℕ} {outside : List ℕ}

def referenceAverage (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hq : q∈outside) (hV : ∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (g : ZMod q→ℂ) (Xp Xm : (ZMod q)ˣ) : ℂ :=
  orderedCorrelation σ
    (bulkDiagram h hs (supported_regular h hs hq hV) (denominatorUnit hs hq) Xp Xm)
    (bulkDiagram k ks (supported_regular k ks hq hV) (denominatorUnit hs hq) Xp Xm) g

theorem referenceAverage_eq_slotCorrelation (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hq : q∈outside) (hV : ∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (g : ZMod q→ℂ) (Xp Xm : (ZMod q)ˣ) :
    referenceAverage h k hs ks hq hV σ g Xp Xm=
      slotCorrelation (haarPermutation σ)
        (bulkDiagram h hs (supported_regular h hs hq hV) (denominatorUnit hs hq) Xp Xm)
        (bulkDiagram k ks (supported_regular k ks hq hV) (denominatorUnit hs hq) Xp Xm) g :=
  orderedCorrelation_eq_slotCorrelation _ _ _ _

theorem referenceAverage_actual_universal (d : Decomposition) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hq : q∈outside) (hV : ∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (hm : 0 < m) (hthree : 3≤q)
    (Xp Xm : (ZMod q)ˣ) :
    ‖referenceAverage h k hs ks hq hV σ (residueTransform d q) Xp Xm‖≤(3:ℝ)^(2^l) :=
  orderedCorrelation_actual_universal d σ hm _ _ hthree

theorem referenceAverage_actual_good (d : Decomposition) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hq : q∈outside) (hV : ∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (hm : 0 < m) (hthree : 3≤q)
    (hgood : ¬Conclusion.TransferBadArrangement σ) (Xp Xm : (ZMod q)ˣ) :
    ‖referenceAverage h k hs ks hq hV σ (residueTransform d q) Xp Xm‖≤
      Tree.treeComparisonConstant (l-2)*
        ((FiniteField.correlationBound (residueTransform d q):ℝ)+(q:ℝ)^(-(1/4:ℝ))) :=
  orderedCorrelation_actual_good_haar d σ hm _ _ hthree
    (PermutationHaarConvention.haarPermutation_good σ hgood)

end Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverage

end

end OAI
