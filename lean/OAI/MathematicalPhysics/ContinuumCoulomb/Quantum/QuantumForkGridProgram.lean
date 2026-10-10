import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListCellIteration
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialStateProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedRawCells

namespace OAI

/-! Actual row/column arrays for the fork compiler. The scale remains an
input register; only the number of fork rounds is fixed. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkGridProgram
open QuantumForkList ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev Cells := QuantumForkList.State × List QuantumRouteCode.Pair
def cellsCode : Cells → List Bool := prodCode QuantumForkList.stateCode (listCode QuantumRouteCode.pairCode)
def queryCode : (ℕ × Cells) → List Bool := prodCode Nat.bits cellsCode
def lookup (xs : List QuantumRouteCode.Pair) (i : ℕ) : QuantumRouteCode.Pair := (xs.drop i).headD (0,0)

noncomputable def nextCellProgram : Procedure queryCode QuantumRouteCode.pairCode
    (fun x => nextCell x.2.1 (lookup x.2.2) x.1) := by
  let v := Procedure.first Nat.bits cellsCode
  let env := Procedure.second Nat.bits cellsCode
  let s := (Procedure.first QuantumForkList.stateCode (listCode QuantumRouteCode.pairCode)).comp env
  let xs := (Procedure.second QuantumForkList.stateCode (listCode QuantumRouteCode.pairCode)).comp env
  let n := Procedure.unaryToBits.comp (countProgram.comp s)
  let before := Procedure.binaryLt.comp (v.pair n)
  let pair := Procedure.binaryDiv.comp
    ((Procedure.binarySub.comp (v.pair n)).pair (Procedure.constant queryCode Nat.bits 2))
  let ps := catalogProgram.comp (groupsProgram.comp s)
  let center := (Procedure.first Nat.bits QuantumForkList.pairCode).comp
    ((Procedure.listGet taggedCode (0,((0,0),(0,0)))).comp (pair.pair ps))
  let target := Procedure.conditional before v center
  exact ((Procedure.listGet QuantumRouteCode.pairCode (0,0)).comp (target.pair xs)).congrFun (by
    intro x
    change lookup x.2.2 (if decide (x.1<x.2.1.1) then x.1 else
      (((catalog x.2.1.2.2.2).drop ((x.1-x.2.1.1)/2)).headD (0,((0,0),(0,0)))).1) = _
    unfold nextCell
    by_cases h : x.1<x.2.1.1 <;> simp [h])

def nextCells (x : Cells) : List QuantumRouteCode.Pair :=
  (List.range (x.1.1+2*pairCount x.1.2.2.2)).map (nextCell x.1 (lookup x.2))

noncomputable def nextCellsProgram : Procedure cellsCode (listCode QuantumRouteCode.pairCode) nextCells := by
  let s := Procedure.first QuantumForkList.stateCode (listCode QuantumRouteCode.pairCode)
  let n := countProgram.comp s
  let pairs := pairCountProgram.comp (groupsProgram.comp s)
  let count := Procedure.unaryAdd.comp (n.pair (Procedure.unaryAdd.comp (pairs.pair pairs)))
  let query : Procedure (prodCode unaryCode cellsCode) queryCode (fun x => (x.1,x.2)) :=
    (Procedure.unaryToBits.comp (Procedure.first unaryCode cellsCode)).pair
      (Procedure.second unaryCode cellsCode)
  let entry := nextCellProgram.comp query
  exact ((Procedure.tabulate (f := fun x i => nextCell x.1 (lookup x.2) i) (0,0) entry).comp
    (count.pair (Procedure.identity cellsCode))).congrFun (by
      intro x
      change (List.range (x.1.1+(pairCount x.1.2.2.2+pairCount x.1.2.2.2))).map _=nextCells x
      simp only [nextCells,two_mul,id_eq])

abbrev Input := ℚ × Cells
def inputCode : Input → List Bool := prodCode ratCode cellsCode
def step (x : Input) : Cells := (next x.1 x.2.1,nextCells x.2)

noncomputable def stepProgram : Procedure inputCode cellsCode step := by
  let scale := Procedure.first ratCode cellsCode
  let env := Procedure.second ratCode cellsCode
  let s := (Procedure.first QuantumForkList.stateCode (listCode QuantumRouteCode.pairCode)).comp env
  exact (nextProgram.comp (scale.pair s)).pair (nextCellsProgram.comp env)

def run : ℕ → Input → Cells
  | 0,x => x.2
  | k+1,x => step (x.1,run k x)

noncomputable def runProgram : (k : ℕ) → Procedure inputCode cellsCode (run k)
  | 0 => Procedure.second ratCode cellsCode
  | k+1 => stepProgram.comp ((Procedure.first ratCode cellsCode).pair (runProgram k))

theorem run_state (k : ℕ) (x : Input) : (run k x).1=iterate x.1 k x.2.1 := by
  induction k with
  | zero => rfl
  | succ k ih => change next x.1 (run k x).1=next x.1 (iterate x.1 k x.2.1); rw [ih]

theorem run_length (k : ℕ) (x : Input) (h : x.2.2.length=x.2.1.1) :
    (run k x).2.length=(run k x).1.1 := by
  cases k with
  | zero => exact h
  | succ k => simp only [run,step,nextCells,List.length_map,List.length_range,next]

def Represents (x : Cells) (cell : ℕ → QuantumRouteCode.Pair) : Prop :=
  ∀ v, v<x.1.1 → lookup x.2 v=cell v

theorem lookup_nextCells (x : Cells) (v : ℕ) (hv : v<x.1.1+2*pairCount x.1.2.2.2) :
    lookup (nextCells x) v=nextCell x.1 (lookup x.2) v := by
  simp only [lookup,nextCells,List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_map,List.length_range] using hv)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

theorem nextCell_congr (s : QuantumForkList.State) (hs : ValidPorts s.1 s.2.2.2)
    (f g : ℕ → QuantumRouteCode.Pair) (h : ∀ v, v<s.1 → f v=g v) (v : ℕ)
    (hv : v<(next 0 s).1) : nextCell s f v=nextCell s g v := by
  by_cases ho : v<s.1
  · simpa only [nextCell,ite_eq_left ho] using h v ho
  have hi : (v-s.1)/2<pairCount s.2.2.2 := by
    change v<s.1+2*pairCount s.2.2.2 at hv
    omega
  simp only [nextCell,ite_eq_right ho]
  rw [catalog_actualSite hs ⟨(v-s.1)/2,hi⟩]
  exact h _ (actualSite hs ⟨(v-s.1)/2,hi⟩ 0).isLt

theorem step_represents (x : Input) (hs : ValidPorts x.2.1.1 x.2.1.2.2.2)
    (cell : ℕ → QuantumRouteCode.Pair) (h : Represents x.2 cell) :
    Represents (step x) (nextCell x.2.1 cell) := by
  intro v hv
  change lookup (nextCells x.2) v=nextCell x.2.1 cell v
  rw [lookup_nextCells x.2 v hv]
  exact nextCell_congr x.2.1 hs _ _ h v hv

theorem run_represents (k : ℕ) (x : Input) (hs : ValidPorts x.2.1.1 x.2.1.2.2.2)
    (cell : ℕ → QuantumRouteCode.Pair) (h : Represents x.2 cell) :
    Represents (run k x) (iterateCell x.1 k x.2.1 cell) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have hi : ValidPorts (run k x).1.1 (run k x).1.2.2.2 := by
      rw [run_state]
      exact iterate_validPorts x.1 x.2.1 hs k
    have hn := step_represents (x.1,run k x) hi _ ih
    simpa only [run_state,run,iterateCell] using hn

end ContinuumCoulomb.QuantumForkGridProgram

end

end OAI
