import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialRoutingTape
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRouteRepresentation

namespace OAI

/-! The computed port paths decorate the actual full bond list with its
remaining subdivision work. Erasing that work leaves the same Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortScheduleTape
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode

abbrev Environment := List Bond × List (List Pair)
def environmentCode : Environment → List Bool :=
  prodCode (listCode bondCode) (listCode (listCode pairCode))
def queryCode : (ℕ × Environment) → List Bool := prodCode unaryCode environmentCode

def entry (x : ℕ × Environment) : QuantumListSchedule.Entry :=
  ((((x.2.2.drop x.1).headD []).length-1),(x.2.1.drop x.1).headD zeroBond)

noncomputable opaque entryProgram : Procedure queryCode QuantumListSchedule.entryCode entry := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode environmentCode)
  let env := Procedure.second unaryCode environmentCode
  let bs := (Procedure.first (listCode bondCode) (listCode (listCode pairCode))).comp env
  let ps := (Procedure.second (listCode bondCode) (listCode (listCode pairCode))).comp env
  let p := (Procedure.listGet (listCode pairCode) []).comp (i.pair ps)
  let len := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp p
  let work := Procedure.unarySub.comp
    (len.pair (Procedure.constant queryCode unaryCode 1))
  let b := (Procedure.listGet bondCode zeroBond).comp (i.pair bs)
  exact work.pair b

def entries (x : Environment) : List QuantumListSchedule.Entry :=
  (List.range x.1.length).map (fun i => entry (i,x))

noncomputable opaque entriesProgram : Procedure environmentCode
    (listCode QuantumListSchedule.entryCode) entries := by
  let bs := Procedure.first (listCode bondCode) (listCode (listCode pairCode))
  let n := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp bs
  let tab : Procedure queryCode (listCode QuantumListSchedule.entryCode)
      (fun x => (List.range x.1).map (fun i => entry (i,x.2))) :=
    Procedure.tabulate (f := fun x i => entry (i,x)) QuantumListSchedule.zeroEntry entryProgram
  exact (tab.comp (n.pair (Procedure.identity environmentCode))).congrFun (by intro x; rfl)

theorem erase_entries (x : Environment) : QuantumListSchedule.erase (entries x) = x.1 := by
  apply List.ext_getElem
  · simp only [QuantumListSchedule.erase,entries,List.length_map,List.length_range]
  · intro i hi hj
    simp only [QuantumListSchedule.erase,entries,List.getElem_map,List.getElem_range,
      entry,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hj,Option.getD_some]

theorem entries_ofFn {m : ℕ} (bs : Fin m → Bond) (ps : Fin m → List Pair) :
    entries (List.ofFn bs,List.ofFn ps) = List.ofFn (fun i => ((ps i).length-1,bs i)) := by
  apply List.ext_getElem
  · simp only [entries,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hi' : i < m := by simpa only [List.length_ofFn] using hj
    simp only [entries,List.length_ofFn,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      entry,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn,
      dite_eq_left hi',Option.getD_some]

theorem allRouted_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    QuantumPortChainProgram.allRouted A B (QuantumRoutingInputProgram.actualData M labels) =
      List.ofFn (fun i : Fin m =>
        (List.range (2*(M.withOrdinalSlots labels).coarseLength hd (labels.symm i)+2)).map
          (qmaPortChain ((M.withOrdinalSlots labels).coarseRoute hd (labels.symm i))
            ((M.withOrdinalSlots labels).coarseLength hd (labels.symm i)))) := by
  apply List.ext_getElem
  · simp only [QuantumPortChainProgram.allRouted,QuantumRoutingInputProgram.actualData,
      List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hi' : i < m := by simpa only [List.length_ofFn] using hj
    have h := QuantumPortChainProgram.routed_actual M labels hA hd (labels.symm ⟨i,hi'⟩)
    simpa only [QuantumPortChainProgram.allRouted,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,Equiv.apply_symm_apply] using h

def value (A B : ℕ) (x : QuantumForkGridProgram.Cells) : QuantumListRouteProgram.State :=
  let d := QuantumForkRoutingData.value x
  ((x.1.1,x.1.2.2.1,entries (QuantumForkList.fullList x.1,QuantumRoutingFamily.coarse A B d)),
    (QuantumRoutingFamily.positions A B d).map qmaExpandedPoint,
    QuantumPortChainProgram.allRouted A B d)

noncomputable opaque program (A B : ℕ) : Procedure QuantumForkGridProgram.cellsCode
    QuantumListRouteProgram.stateCode (value A B) := by
  let s := Procedure.first QuantumForkList.stateCode (listCode pairCode)
  let n := QuantumForkList.countProgram.comp s
  let c := (Procedure.first ratCode QuantumForkList.groupsCode).comp
    ((Procedure.second (listCode bondCode) (prodCode ratCode QuantumForkList.groupsCode)).comp
      ((Procedure.second unaryCode
        (prodCode (listCode bondCode) (prodCode ratCode QuantumForkList.groupsCode))).comp s))
  let bs := QuantumForkRoutingData.fullProgram.comp s
  let d := QuantumForkRoutingData.program
  let ps := (QuantumRoutingFamily.coarseProgram A B).comp d
  let es := entriesProgram.comp (bs.pair ps)
  let positions := (Procedure.listMap (0,0) (0,0) QuantumPortChainProgram.centerProgram).comp
    ((QuantumRoutingFamily.positionsProgram A B).comp d)
  let paths := (QuantumPortChainProgram.allRoutedProgram A B).comp d
  exact (n.pair (c.pair es)).pair (positions.pair paths)

theorem value_erase (A B : ℕ) (x : QuantumForkGridProgram.Cells) :
    QuantumListSchedule.erase (value A B x).1.2.2 = QuantumForkList.fullList x.1 :=
  erase_entries _

theorem value_valid (A B : ℕ) (x : QuantumForkGridProgram.Cells)
    (hs : QuantumForkList.ValidPorts x.1.1 x.1.2.2.2)
    (hb : SourceBondLists.bounded x.1.1 x.1.2.1)
    (hn : ∀ b ∈ x.1.2.1, b.1≠b.2.1) : QuantumListSchedule.Valid (value A B x).1 := by
  constructor
  · rw [value_erase]
    exact QuantumForkList.fullList_bounded x.1 hs hb
  · rw [value_erase]
    exact QuantumForkList.fullList_noLoops x.1 hs hn

theorem value_energy (A B : ℕ) (x : QuantumForkGridProgram.Cells)
    (hs : QuantumForkList.ValidPorts x.1.1 x.1.2.2.2)
    (hb : SourceBondLists.bounded x.1.1 x.1.2.1)
    (hn : ∀ b ∈ x.1.2.1, b.1≠b.2.1) :
    QuantumListSchedule.energy (value A B x).1 =
      (QuantumForkList.fullGraph x.1 hs hb hn).energy := by
  unfold QuantumListSchedule.energy
  rw [value_erase]
  exact (QuantumListGraph.ofBonds_energy x.1.1 (QuantumForkList.fullList x.1) x.1.2.2.1
    (QuantumForkList.fullList_bounded x.1 hs hb)
    (QuantumForkList.fullList_noLoops x.1 hs hn)).symm

end ContinuumCoulomb.QuantumPortScheduleTape

end

end OAI
