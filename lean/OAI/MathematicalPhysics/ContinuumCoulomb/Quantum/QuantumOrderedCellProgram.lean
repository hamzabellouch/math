import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingInputProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawFamilyProgram

namespace OAI

/-! Cell arrays follow the same term-major order as the literal local-word
compiler. Each new mediator inherits its term's cell; each output word retains
that cell as its anchor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedCellProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev State := List Pair × List Pair
def stateCode : State → List Bool := prodCode (listCode pairCode) (listCode pairCode)

def anchors (d : ℕ) (xs : List Pair) : List Pair :=
  (xs.map (fun p => List.replicate d p)).flatten

def value (d : ℕ) (x : State) : State := (x.1++x.2,anchors d x.2)

noncomputable def repeatProgram (d : ℕ) :
    Procedure pairCode (listCode pairCode) (fun p : Pair => List.replicate d p) :=
  (QuantumRawExchange.fixedListProgram pairCode pairCode d (fun _ p => p)
    (fun _ => Procedure.identity pairCode)).congrFun (by intro p; simp)

noncomputable def anchorsProgram (d : ℕ) :
    Procedure (listCode pairCode) (listCode pairCode) (anchors d) :=
  (QuantumRawExchange.flattenProgram pairCode (0,0)).comp
    (Procedure.listMap (0,0) [] (repeatProgram d))

noncomputable def program (d : ℕ) : Procedure stateCode stateCode (value d) :=
  (Procedure.listAppend pairCode (0,0)).pair
    ((anchorsProgram d).comp (Procedure.second (listCode pairCode) (listCode pairCode)))

theorem cells_length (d : ℕ) (x : State) : (value d x).1.length=x.1.length+x.2.length :=
  List.length_append

theorem anchors_length (d : ℕ) (xs : List Pair) : (anchors d xs).length=xs.length*d := by
  induction xs with
  | nil => simp [anchors]
  | cons p xs ih =>
    simp only [anchors,List.map_cons,List.flatten_cons,List.length_append,List.length_replicate] at *
    rw [ih,List.length_cons]
    simp only [Nat.add_mul,Nat.one_mul]
    omega

theorem cells_ofFn {n m : ℕ} (d : ℕ) (cell : Fin n → Pair) (anchor : Fin m → Pair) :
    (value d (List.ofFn cell,List.ofFn anchor)).1=List.ofFn (Fin.append cell anchor) :=
  (List.ofFn_fin_append cell anchor).symm

theorem anchors_ofFn {m : ℕ} (d : ℕ) (anchor : Fin m → Pair) :
    anchors d (List.ofFn anchor)=
      (List.ofFn (fun i : Fin m => List.ofFn (fun _ : Fin d => anchor i))).flatten := by
  simp only [anchors,List.map_ofFn,List.ofFn_const,Function.comp_def]

end ContinuumCoulomb.QuantumOrderedCellProgram

end

end OAI
