import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedLabelProgram

namespace OAI

/-! Every emitted local packet entry is the actual padded history word
and its sampled coefficient, in the supplied support-list order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open scoped Classical

-- The padded scalar table uses this same finite-domain decision.  Matching it
-- keeps the fixed matrix enumeration opaque during the source-entry proof.
local instance finDecision (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

private theorem labels_eq_zip (n m : ℕ) (w : Fin (n+m) → Fin 4)
    (xs : List ℕ) (hlen : xs.length=n) :
    labels n m w xs = xs.zip (localLabels n m w) := by
  apply List.ext_getElem
  · simp [labels,localLabels,hlen]
  · intro i hi hj
    have hi' : i < xs.length := by simpa only [labels,List.length_ofFn,← hlen] using hi
    simp only [labels,localLabels,List.getElem_ofFn,List.getElem_zip]
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi',Option.getD_some]

theorem entry_source (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (w : Fin ((QuantumOrderedSupport.sites c hT a).length+
      (6-(QuantumOrderedSupport.sites c hT a).length)) → Fin 4) :
    entry (QuantumOrderedSupport.sites c hT a).length
      (6-(QuantumOrderedSupport.sites c hT a).length) w
      (k,QuantumOrderedSupport.encodedSites c hT a,
        matrixData (QuantumAlgebraicHistory.orderedTable c hT a)) =
    let p : Term c := (a,(widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).symm w)
    (QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT a) (word c hT p),sampledWeight k c hT p) := by
  let p : Term c := (a,(widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).symm w)
  have hw : widthIndex _ (QuantumOrderedSupport.sites_length c hT a) p.2 = w :=
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).apply_symm_apply w
  apply Prod.ext
  · change labels _ _ w (QuantumOrderedSupport.encodedSites c hT a) = _
    rw [labels_eq_zip _ _ w _ (by simp only [QuantumOrderedSupport.encodedSites,List.length_map])]
    have hs := source_tag c hT p
    change QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT a) (word c hT p) =
      (QuantumOrderedSupport.encodedSites c hT a).zip (localLabels _ _
        (widthIndex _ (QuantumOrderedSupport.sites_length c hT a) p.2)) at hs
    rw [hw] at hs
    exact hs.symm
  · change sample k (QuantumPaddedTable.coefficient _ _ _ w) = _
    unfold sampledWeight
    apply congrArg (sample k)
    unfold scalar
    rw [hw]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
