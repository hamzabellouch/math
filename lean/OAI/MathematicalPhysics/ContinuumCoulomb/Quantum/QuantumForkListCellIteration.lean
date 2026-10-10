import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListCellProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListCellLocality
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListNext

namespace OAI

/-! The finite label array computed by each literal round represents the
geometric cell map at every emitted spin. Fixed-round iteration is polynomial. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

def RepresentsCells (s : State) (xs : List ℕ) (cell : ℕ → ℕ) : Prop :=
  ∀ v, v<s.1 → cellAt xs v=cell v

theorem cellAt_nextCells (x : CellInput) (v : ℕ)
    (hv : v<x.1.1+2*pairCount x.1.2.2.2) :
    cellAt (nextCells x) v=nextCell x.1 (cellAt x.2) v := by
  simp only [cellAt,nextCells,List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_map,List.length_range] using hv)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

theorem nextCell_congr (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (f g : ℕ → ℕ) (h : ∀ v, v<s.1 → f v=g v) (v : ℕ)
    (hv : v<(next 0 s).1) : nextCell s f v=nextCell s g v := by
  by_cases ho : v<s.1
  · simpa only [nextCell,ite_eq_left ho] using h v ho
  have hi : (v-s.1)/2<pairCount s.2.2.2 := by
    change v<s.1+2*pairCount s.2.2.2 at hv
    omega
  simp only [nextCell,ite_eq_right ho]
  rw [catalog_actualSite hs ⟨(v-s.1)/2,hi⟩]
  exact h _ (actualSite hs ⟨(v-s.1)/2,hi⟩ 0).isLt

theorem next_representsCells (N : ℚ) (x : CellInput)
    (hs : ValidPorts x.1.1 x.1.2.2.2) (cell : ℕ → ℕ)
    (h : RepresentsCells x.1 x.2 cell) :
    RepresentsCells (next N x.1) (nextCells x) (nextCell x.1 cell) := by
  intro v hv
  rw [cellAt_nextCells x v hv]
  exact nextCell_congr x.1 hs _ _ h v hv

def cellStep (N : ℚ) (x : CellInput) : CellInput := (next N x.1,nextCells x)

noncomputable def cellStepProgram (N : ℚ) :
    Procedure cellInputCode cellInputCode (cellStep N) :=
  (nextProgram.comp ((Procedure.constant cellInputCode ratCode N).pair
    (Procedure.first stateCode (listCode Nat.bits)))).pair nextCellsProgram

def cellIterate (N : ℚ) : ℕ → CellInput → CellInput
  | 0,x => x
  | k+1,x => cellStep N (cellIterate N k x)

noncomputable def cellIterateProgram (N : ℚ) :
    (k : ℕ) → Procedure cellInputCode cellInputCode (cellIterate N k)
  | 0 => Procedure.identity cellInputCode
  | k+1 => (cellStepProgram N).comp (cellIterateProgram N k)

theorem cellIterate_state (N : ℚ) (k : ℕ) (x : CellInput) :
    (cellIterate N k x).1=iterate N k x.1 := by
  induction k with
  | zero => rfl
  | succ k ih => change next N (cellIterate N k x).1=next N (iterate N k x.1); rw [ih]

theorem cellIterate_represents (N : ℚ) (k : ℕ) (x : CellInput)
    (hs : ValidPorts x.1.1 x.1.2.2.2) (cell : ℕ → ℕ)
    (h : RepresentsCells x.1 x.2 cell) :
    RepresentsCells (iterate N k x.1) (cellIterate N k x).2 (iterateCell N k x.1 cell) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have hi : ValidPorts (cellIterate N k x).1.1 (cellIterate N k x).1.2.2.2 := by
      rw [cellIterate_state]
      exact iterate_validPorts N x.1 hs k
    have hr : RepresentsCells (cellIterate N k x).1 (cellIterate N k x).2
        (iterateCell N k x.1 cell) := by simpa only [cellIterate_state] using ih
    have hn := next_representsCells N (cellIterate N k x) hi _ hr
    simpa only [cellIterate_state,cellIterate,cellStep,iterate,iterateCell] using hn

end ContinuumCoulomb.QuantumForkList

end

end OAI
