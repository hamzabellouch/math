import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedLabelMeaning
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSourceIndex

namespace OAI

/-! The literal concatenation of fixed-width history packets is an exact
enumeration of the actual padded history family.  The local pattern order is
allowed to depend on the support width; its explicit bijection is retained. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open scoped Classical

private theorem pattern_card (n : ℕ) (hn : n ≤ 6) :
    Fintype.card (Fin (n+(6-n)) → Fin 4) = QuantumOrderedSourceIndex.patternCount := by
  simp only [QuantumOrderedSourceIndex.patternCount,QuantumOrderedSourceIndex.Pattern,
    Fintype.card_fun,Fintype.card_fin,Nat.add_sub_of_le hn]

def packetPatterns (n : ℕ) (hn : n ≤ 6) :
    Fin QuantumOrderedSourceIndex.patternCount ≃ (Fin (n+(6-n)) → Fin 4) :=
  (finCongr (pattern_card n hn).symm).trans (Fintype.equivFin _).symm

theorem packet_reindex (n : ℕ) (hn : n ≤ 6) (x : Input) :
    packet n (6-n) x = List.ofFn (fun j => entry n (6-n) (packetPatterns n hn j) x) := by
  simp only [packet,enumerate,List.map_ofFn,Function.comp_def]
  rw [List.ofFn_congr (pattern_card n hn)]
  rfl

local instance tableFinDecision (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def sourceInput (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) : Input :=
  (k,QuantumOrderedSupport.encodedSites c hT a,
    matrixData (QuantumAlgebraicHistory.orderedTable c hT a))

def sourceEntries (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    List QuantumOrderedLabelFamily.Entry :=
  (List.ofFn (fun i : Fin (QuantumOrderedSourceIndex.referenceCount c) =>
    uniformPacket (sourceInput k c hT (QuantumOrderedSourceIndex.reference c i)))).flatten

def sourceTerms (c : QMACircuit) (hT : 0 < c.gates.length) :
    Fin (QuantumOrderedSourceIndex.referenceCount c*QuantumOrderedSourceIndex.patternCount) ≃ Term c :=
  finProdFinEquiv.symm.trans (Equiv.prodShear (QuantumOrderedSourceIndex.reference c)
    (fun i =>
      let a := QuantumOrderedSourceIndex.reference c i
      let hn := QuantumOrderedSupport.sites_length c hT a
      (packetPatterns _ hn).trans (widthIndex _ hn).symm))

def sourceWord (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    QuantumOrderedSupport.Qubit c → Fin 4 := word c hT p

theorem sourceEntries_table (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    sourceEntries k c hT =
      QuantumOrderedLabelTable.table (sourceTerms c hT)
        (QuantumOrderedLabelTable.index (QuantumOrderedSourceIndex.qubits c))
        (fun p => QuantumOrderedSupport.sites c hT p.1)
        (sourceWord c hT) (sampledWeight k c hT) := by
  unfold sourceEntries QuantumOrderedLabelTable.table sourceTerms
  simp only [Equiv.trans_apply]
  let entryAt (j : Fin (QuantumOrderedSourceIndex.referenceCount c) ×
      Fin QuantumOrderedSourceIndex.patternCount) :=
    let p := Equiv.prodShear (QuantumOrderedSourceIndex.reference c)
      (fun i => (packetPatterns _ (QuantumOrderedSupport.sites_length c hT
        (QuantumOrderedSourceIndex.reference c i))).trans
          (widthIndex _ (QuantumOrderedSupport.sites_length c hT
            (QuantumOrderedSourceIndex.reference c i))).symm) j
    (QuantumOrderedLabelData.tag
      (QuantumOrderedLabelTable.index (QuantumOrderedSourceIndex.qubits c))
      (QuantumOrderedSupport.sites c hT p.1) (sourceWord c hT p),sampledWeight k c hT p)
  change _ = List.ofFn (fun i => entryAt (finProdFinEquiv.symm i))
  rw [QuantumOrderedLabelTable.product_table entryAt]
  dsimp only [entryAt]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  let a := QuantumOrderedSourceIndex.reference c i
  have hn := QuantumOrderedSupport.sites_length c hT a
  rw [uniformPacket_eq _ (by
    simpa only [sourceInput,QuantumOrderedSupport.encodedSites,List.length_map] using hn)]
  rw [show (sourceInput k c hT (QuantumOrderedSourceIndex.reference c i)).2.1.length =
    (QuantumOrderedSupport.sites c hT a).length by
      simp only [sourceInput,QuantumOrderedSupport.encodedSites,List.length_map,a]]
  change packet (QuantumOrderedSupport.sites c hT a).length
    (6-(QuantumOrderedSupport.sites c hT a).length) (sourceInput k c hT a) = _
  rw [packet_reindex _ hn]
  apply congrArg List.ofFn
  funext j
  have h := entry_source k c hT a (packetPatterns _ hn j)
  simpa only [sourceInput,sourceWord,Equiv.trans_apply,Equiv.prodShear_apply,
    Equiv.symm_apply_apply,
    QuantumOrderedSourceIndex.qubits_index] using h

theorem sourceEntries_length (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    (sourceEntries k c hT).length = QuantumOrderedSourceIndex.termCount c := by
  rw [sourceEntries_table]
  simp only [QuantumOrderedLabelTable.table,List.length_ofFn,
    QuantumOrderedSourceIndex.termCount]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
