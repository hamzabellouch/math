import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.ExpanderTables

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.ExpanderRowControl

open ExpanderTables

abbrev degree (d : Nat) : Nat := d * d
abbrev cloudSize (d : Nat) : Nat := degree d * degree d
abbrev rowFactor (d : Nat) : Nat := cloudSize d * degree d

structure Control (d : Nat) where
  firstH : Fin (cloudSize d) × Fin d
  lastInput : Fin d
  firstG : Fin (degree d)
  secondG : Fin (degree d)
  lastH : Fin (cloudSize d) × Fin d
  deriving DecidableEq, Fintype

def squarePorts {d : Nat} (s : Control d) : Fin (degree d) × Fin (degree d) :=
  (rowIndex (degree d) (degree d)).symm s.firstH.1

def start {d : Nat} (H : Table (cloudSize d) d)
    (cloud : Fin (cloudSize d)) (port : Fin (degree d)) : Control d :=
  let ports := (rowIndex d d).symm port
  let first := lookup H (cloud, ports.1)
  let square := (rowIndex (degree d) (degree d)).symm first.1
  { firstH := first
    lastInput := ports.2
    firstG := square.1
    secondG := square.2
    lastH := first }

def receiveFirst {d : Nat} (s : Control d) (returnedPort : Fin (degree d)) : Control d :=
  { s with firstG := returnedPort }

def receiveSecond {d : Nat} (H : Table (cloudSize d) d)
    (s : Control d) (returnedPort : Fin (degree d)) : Control d :=
  { s with
    secondG := returnedPort
    lastH := lookup H
      (rowIndex (degree d) (degree d) (returnedPort,s.firstG),s.lastInput) }

def firstOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).1
def secondOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).2

def outputPort {d : Nat} (s : Control d) : Fin (degree d) :=
  rowIndex d d (s.lastH.2,s.firstH.2)

def outputOffset {d : Nat} (s : Control d) : Fin (rowFactor d) :=
  rowIndex (cloudSize d) (degree d) (s.lastH.1,outputPort s)

def firstAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  degree d * vertex + (firstOffset s).val

def secondAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  degree d * vertex + (secondOffset s).val

def outputAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  rowFactor d * vertex + (outputOffset s).val

@[simp] theorem firstOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    firstOffset (receiveFirst s r) = firstOffset s := rfl

@[simp] theorem secondOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    secondOffset (receiveFirst s r) = secondOffset s := rfl

@[simp] theorem receiveFirst_port {d : Nat} (s : Control d) (r : Fin (degree d)) :
    (receiveFirst s r).firstG = r := rfl

@[simp] theorem receiveSecond_port {d : Nat} (H : Table (cloudSize d) d)
    (s : Control d) (r : Fin (degree d)) : (receiveSecond H s r).secondG = r := rfl

theorem firstAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    firstAddress vertex.val s =
      (rowIndex v (degree d) (vertex,firstOffset s)).val := by
  rw [rowIndex_val]
  exact Nat.add_comm _ _

theorem secondAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    secondAddress vertex.val s =
      (rowIndex v (degree d) (vertex,secondOffset s)).val := by
  rw [rowIndex_val]
  exact Nat.add_comm _ _

theorem firstAddress_lt {v d : Nat} (vertex : Fin v) (s : Control d) :
    firstAddress vertex.val s < v * degree d := by
  rw [firstAddress_eq_rowIndex]
  exact (rowIndex v (degree d) (vertex,firstOffset s)).isLt

theorem secondAddress_lt {v d : Nat} (vertex : Fin v) (s : Control d) :
    secondAddress vertex.val s < v * degree d := by
  rw [secondAddress_eq_rowIndex]
  exact (rowIndex v (degree d) (vertex,secondOffset s)).isLt

theorem lookup_vertex_div {v q : Nat} (G : Table v q) (x : Fin v × Fin q) :
    (lookup G x).1.val = (reverseIndex G (rowIndex v q x)).val / q := rfl

theorem lookup_port_mod {v q : Nat} (G : Table v q) (x : Fin v × Fin q) :
    (lookup G x).2.val = (reverseIndex G (rowIndex v q x)).val % q := rfl

theorem lookup_port_eq_remainder {v q : Nat} (G : Table v q) (x : Fin v × Fin q)
    (r : Fin q) (hr : r.val = (reverseIndex G (rowIndex v q x)).val % q) :
    (lookup G x).2 = r := Fin.ext ((lookup_port_mod G x).trans hr.symm)

theorem rowIndex_lookup {v q : Nat} (G : Table v q) (x : Fin v × Fin q) :
    rowIndex v q (lookup G x) = reverseIndex G (rowIndex v q x) := by
  simp only [lookup, Equiv.apply_symm_apply]

def outputPair {v d : Nat} (vertex : Fin v) (s : Control d) :
    Fin (v * cloudSize d) × Fin (degree d) :=
  (rowIndex v (cloudSize d) (vertex,s.lastH.1),outputPort s)

theorem outputAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    outputAddress vertex.val s =
      (rowIndex (v * cloudSize d) (degree d) (outputPair vertex s)).val := by
  simp only [outputAddress, outputOffset, outputPair, rowIndex_val, rowFactor]
  ring

theorem outputAddress_lt {v d : Nat} (vertex : Fin v) (s : Control d) :
    outputAddress vertex.val s < (v * cloudSize d) * degree d := by
  rw [outputAddress_eq_rowIndex]
  exact (rowIndex (v * cloudSize d) (degree d) (outputPair vertex s)).isLt

def evaluateRow {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    Fin v × Control d :=
  let s₀ := start H cloud port
  let g₁ := lookup G (vertex,firstOffset s₀)
  let s₁ := receiveFirst s₀ g₁.2
  let g₂ := lookup G (g₁.1,secondOffset s₁)
  (g₂.1, receiveSecond H s₁ g₂.2)

theorem evaluateRow_eq_lookup_step {v d : Nat}
    (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    outputPair (evaluateRow G H vertex cloud port).1 (evaluateRow G H vertex cloud port).2 =
      lookup (step G H) (rowIndex v (cloudSize d) (vertex,cloud),port) := by
  rw [lookup_step]
  simp only [evaluateRow, start, receiveFirst, receiveSecond, firstOffset, secondOffset,
    squarePorts, outputPair, outputPort, stepLookup, Equiv.symm_apply_apply]

theorem outputAddress_eq_step_row {v d : Nat}
    (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    outputAddress (evaluateRow G H vertex cloud port).1.val (evaluateRow G H vertex cloud port).2 =
      (rowIndex (v * cloudSize d) (degree d)
        (lookup (step G H) (rowIndex v (cloudSize d) (vertex,cloud),port))).val := by
  rw [outputAddress_eq_rowIndex, evaluateRow_eq_lookup_step]

theorem outputAddress_eq_step_reverseIndex {v d : Nat}
    (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    outputAddress (evaluateRow G H vertex cloud port).1.val (evaluateRow G H vertex cloud port).2 =
      (reverseIndex (step G H) (rowIndex (v * cloudSize d) (degree d)
        (rowIndex v (cloudSize d) (vertex,cloud),port))).val := by
  rw [outputAddress_eq_step_row, rowIndex_lookup]

end IndependentSetsGames.Foundations.PCP.ExpanderRowControl

end OAI
