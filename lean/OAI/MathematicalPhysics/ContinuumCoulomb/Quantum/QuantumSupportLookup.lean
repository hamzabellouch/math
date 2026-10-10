import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFirstUseProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedTable
import OAI.Computability.QuantumFactoring.BitStackListIndex

namespace OAI

/-! The actual local support coordinates are read by literal label lookup.
This identifies a small matrix input with its zero extension on spectator
qubits, without enumerating the ambient spin basis. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSupportLookup
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ℕ × (List ℕ × List ℕ)
def inputCode : Input → List Bool :=
  prodCode Nat.bits (prodCode (listCode Nat.bits) (listCode Nat.bits))

def value (x : Input) : ℕ := (x.2.2.drop (x.2.1.idxOf x.1)).headD 0

noncomputable def matchesProgram :
    Procedure (prodCode Nat.bits (listCode Nat.bits)) (listCode Procedure.boolCode)
      (fun x => x.2.map (fun a => decide (a=x.1))) :=
  Procedure.listMapWith (f := fun label a => decide (a=label)) 0 false
    (Procedure.binaryEq.comp
      ((Procedure.second Nat.bits Nat.bits).pair (Procedure.first Nat.bits Nat.bits)))

noncomputable def indexProgram :
    Procedure (prodCode Nat.bits (listCode Nat.bits)) Nat.bits
      (fun x => x.2.idxOf x.1) :=
  ((Procedure.unaryToBits.comp QuantumFirstUseProgram.firstProgram).comp matchesProgram).congrFun
    (by
      intro x
      simp only [Function.comp_apply,id_eq]
      rw [QuantumFirstUseProgram.first_eq_findIdx,List.findIdx_map]
      change x.2.findIdx (fun a => decide (a=x.1)) = x.2.findIdx (fun a => a==x.1)
      congr 1)

noncomputable def program : Procedure inputCode Nat.bits value := by
  let label := Procedure.first Nat.bits (prodCode (listCode Nat.bits) (listCode Nat.bits))
  let rest := Procedure.second Nat.bits (prodCode (listCode Nat.bits) (listCode Nat.bits))
  let sites := (Procedure.first (listCode Nat.bits) (listCode Nat.bits)).comp rest
  let bits := (Procedure.second (listCode Nat.bits) (listCode Nat.bits)).comp rest
  exact (Procedure.listGet Nat.bits 0).comp
    ((indexProgram.comp (label.pair sites)).pair bits)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode Nat.bits value :=
  program.toTM2

theorem value_get (xs : List ℕ) (hx : xs.Nodup) (s : Fin xs.length → ℕ)
    (i : Fin xs.length) :
    value (xs.get i,xs,List.ofFn s)=s i := by
  unfold value
  rw [List.get_idxOf hx]
  rw [List.headD_eq_head?_getD,List.head?_drop]
  simp

theorem value_absent (xs : List ℕ) (s : Fin xs.length → ℕ) (q : ℕ)
    (hq : q ∉ xs) : value (q,xs,List.ofFn s)=0 := by
  unfold value
  rw [List.idxOf_of_notMem hq]
  simp

theorem value_map_get {α : Type} (xs : List α) (hx : xs.Nodup)
    (f : α → ℕ) (hf : Function.Injective f) (s : Fin xs.length → ℕ)
    (i : Fin xs.length) :
    value (f (xs.get i),xs.map f,List.ofFn s)=s i := by
  have hi : i.val < (xs.map f).length := by simpa only [List.length_map] using i.isLt
  have he : (xs.map f)[i.val]'hi = f (xs.get i) := by
    simp only [List.getElem_map,List.get_eq_getElem]
  have hind := (hx.map hf).idxOf_getElem i.val hi
  rw [he] at hind
  unfold value
  rw [hind,List.headD_eq_head?_getD,List.head?_drop]
  simp

theorem value_not_mem (xs ys : List ℕ) (q : ℕ)
    (hq : q ∉ xs) (hy : ys.length ≤ xs.length) : value (q,xs,ys)=0 := by
  unfold value
  rw [List.idxOf_of_notMem hq,List.drop_eq_nil_of_le hy]
  rfl

open QuantumOrderedSupport
open scoped Classical

private theorem extend_mem {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (u : QMASupportBasis S) (q : α) (hq : q ∈ S) :
    qmaSupportExtend S u q = u ⟨q,hq⟩ :=
  dite_eq_left hq

private theorem extend_not_mem {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (u : QMASupportBasis S) (q : α) (hq : q ∉ S) :
    qmaSupportExtend S u q = 0 :=
  dite_eq_right hq

def supportBits (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (sites c hT a).length → Fin 2) : List ℕ :=
  List.ofFn (fun i => (s i).val)

theorem support_value (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (sites c hT a).length → Fin 2) (q : Qubit c) :
    value (siteNumber c q,encodedSites c hT a,supportBits c hT a s) =
      (qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun i => s ((supportEquiv c hT a).symm i)) q).val := by
  by_cases hq : q ∈ (qmaOrderedHistoryModel c hT).sites a
  · let i := (supportEquiv c hT a).symm ⟨q,hq⟩
    have hi : (sites c hT a).get i=q := by
      have h := congrArg Subtype.val ((supportEquiv c hT a).apply_symm_apply ⟨q,hq⟩)
      exact h
    have hlookup := value_map_get (sites c hT a) (sites_nodup c hT a)
      (siteNumber c) (siteNumber_injective c) (fun j => (s j).val) i
    have hv : value (siteNumber c q,encodedSites c hT a,supportBits c hT a s) =
        (s i).val := by
      simpa only [encodedSites,supportBits,hi] using hlookup
    exact hv.trans (congrArg Fin.val (extend_mem
      ((qmaOrderedHistoryModel c hT).sites a)
      (fun j => s ((supportEquiv c hT a).symm j)) q hq)).symm
  · have hn : siteNumber c q ∉ encodedSites c hT a := by
      intro h
      obtain ⟨p,hp,he⟩ := List.mem_map.mp h
      have hpq := siteNumber_injective c he
      subst p
      apply hq
      rw [← sites_finset c hT a]
      exact List.mem_toFinset.mpr hp
    have hzero := value_not_mem (encodedSites c hT a) (supportBits c hT a s)
      (siteNumber c q) hn (by simp only [supportBits,List.length_ofFn,
        encodedSites,List.length_map,le_refl])
    have hv : value (siteNumber c q,encodedSites c hT a,supportBits c hT a s) = 0 := by
      exact hzero
    exact hv.trans (congrArg Fin.val (extend_not_mem
      ((qmaOrderedHistoryModel c hT).sites a)
      (fun j => s ((supportEquiv c hT a).symm j)) q hq)).symm

def readBit (x : Input) : Fin 2 := ⟨value x % 2,Nat.mod_lt _ (by decide)⟩

theorem support_readBit (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (sites c hT a).length → Fin 2) (q : Qubit c) :
    readBit (siteNumber c q,encodedSites c hT a,supportBits c hT a s) =
      qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun i => s ((supportEquiv c hT a).symm i)) q := by
  apply Fin.ext
  change value _ % 2 = _
  rw [support_value]
  exact Nat.mod_eq_of_lt (Fin.isLt _)

theorem orderedTable_lookup (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (sites c hT a).length → Fin 2) :
    QuantumAlgebraicHistory.orderedTable c hT a s t =
      QuantumAlgebraicHistory.orderedTerm c hT a
        (fun q => readBit (siteNumber c q,encodedSites c hT a,supportBits c hT a s))
        (fun q => readBit (siteNumber c q,encodedSites c hT a,supportBits c hT a t)) := by
  unfold QuantumAlgebraicHistory.orderedTable QuantumAlgebraicHistory.orderedCore
  congr 1 <;> funext q <;> exact (support_readBit c hT a _ q).symm

end ContinuumCoulomb.QuantumSupportLookup

end

end OAI
