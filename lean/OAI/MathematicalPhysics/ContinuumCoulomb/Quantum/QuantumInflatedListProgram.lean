import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteLeafProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumInflatedPath
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkGridProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRoutePieces

namespace OAI

/-! The eightfold scaled route is an explicit list computation. Its loop
bound is eight times the input route length. -/

noncomputable section
namespace ContinuumCoulomb.QuantumInflatedListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev Input := ℕ × List Pair
def inputCode : Input → List Bool := prodCode Nat.bits (listCode pairCode)
def point (x : Input) : Pair := qmaInflatedPoint (QuantumForkGridProgram.lookup x.2) x.1
def value (xs : List Pair) : List Pair :=
  (List.range (8*(xs.length-1)+1)).map (fun k => point (k,xs))

noncomputable opaque pointProgram : Procedure inputCode pairCode point := by
  let k := Procedure.first Nat.bits (listCode pairCode)
  let xs := Procedure.second Nat.bits (listCode pairCode)
  let eight := Procedure.constant inputCode Nat.bits 8
  let index := Procedure.binaryDiv.comp (k.pair eight)
  let indexNext := Procedure.successor.comp index
  let get := Procedure.listGet pairCode (0,0)
  let p := QuantumRouteLeafCode.centerProgram.comp (get.comp (index.pair xs))
  let q := QuantumRouteLeafCode.centerProgram.comp (get.comp (indexNext.pair xs))
  let rest := Procedure.binaryMod.comp (k.pair eight)
  exact QuantumRouteCode.pointProgram.comp ((p.pair q).pair rest)

noncomputable opaque lengthProgram : Procedure (listCode pairCode) unaryCode
    (fun xs => 8*(xs.length-1)+1) :=
  Procedure.unarySuccessor.comp (Procedure.unaryMul.comp
    ((Procedure.constant (listCode pairCode) unaryCode 8).pair
      (Procedure.unaryPred.comp
        (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)))))

noncomputable opaque indexedProgram : Procedure (prodCode unaryCode (listCode pairCode))
    pairCode (fun x => point (x.1,x.2)) :=
  pointProgram.comp
    ((Procedure.unaryToBits.comp (Procedure.first unaryCode (listCode pairCode))).pair
      (Procedure.second unaryCode (listCode pairCode)))

noncomputable opaque tabProgram : Procedure (prodCode unaryCode (listCode pairCode))
    (listCode pairCode) (fun x => (List.range x.1).map (fun k => point (k,x.2))) :=
  Procedure.tabulate (f := fun xs k => point (k,xs)) (0,0) indexedProgram

noncomputable opaque program : Procedure (listCode pairCode) (listCode pairCode) value :=
  (tabProgram.comp (lengthProgram.pair (Procedure.identity (listCode pairCode)))).congrFun
    (by intro xs; rfl)

theorem length_value (xs : List Pair) : (value xs).length=8*(xs.length-1)+1 := by
  simp only [value,List.length_map,List.length_range]

theorem get_value (xs : List Pair) (k : ℕ) (hk : k < 8*(xs.length-1)+1) :
    (value xs)[k]'(by simpa only [length_value] using hk)=
      qmaInflatedPoint (QuantumForkGridProgram.lookup xs) k := by
  simp only [value,List.getElem_map,List.getElem_range,point]

theorem lookup_range (p : ℕ → Pair) (n k : ℕ) (hk : k<n) :
    QuantumForkGridProgram.lookup ((List.range n).map p) k=p k :=
  QuantumListRouteProgram.lookup_range p n k hk

theorem point_range (p : ℕ → Pair) (L k : ℕ) (hk : k≤8*L) :
    point (k,(List.range (L+1)).map p)=qmaInflatedPoint p k := by
  unfold point
  by_cases he : k=8*L
  · subst k
    rw [qmaInflatedPoint_last,qmaInflatedPoint_last,
      lookup_range p (L+1) L (by omega)]
  · have hd : k/8<L := by omega
    unfold qmaInflatedPoint
    rw [lookup_range p (L+1) (k/8) (by omega),
      lookup_range p (L+1) (k/8+1) (by omega)]

theorem value_range (p : ℕ → Pair) (L : ℕ) :
    value ((List.range (L+1)).map p)=
      (List.range (8*L+1)).map (qmaInflatedPoint p) := by
  unfold value
  simp only [List.length_map,List.length_range,Nat.add_sub_cancel]
  apply List.map_congr_left
  intro k hk
  exact point_range p L k (by have := List.mem_range.mp hk; omega)

end ContinuumCoulomb.QuantumInflatedListProgram

end

end OAI
