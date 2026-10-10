import OAI.Combinatorics.LowSpaceSubsetSum.Storage.FiniteSetCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.ComputedParentFuels

namespace OAI

/-! # Constant-state loop limits and their live domain scans

The length, binomial, and doubling loops retain scalar accumulators only.
No leaf occurrence is enumerated. The three domain lists are retained
through the scalar computation and released when the leaf limit returns.
-/

namespace LowSpaceSubsetSum.ComputedFuelCells

variable {n : ℕ}

def lengthLoop {α : Type*} : List α → ℕ → ℕ → (ℕ × ℕ) × ℕ
  | [], value, work => ((value, work+1), 8)
  | _ :: xs, value, work => lengthLoop xs (value+1) (work+2)

theorem lengthLoop_formula {α : Type*} (xs : List α) (value work : ℕ) :
    lengthLoop xs value work = ((value+xs.length, work+2*xs.length+1), 8) := by
  induction xs generalizing value work with
  | nil => simp only [lengthLoop, List.length_nil, Nat.add_zero, Nat.mul_zero]
  | cons x xs ih =>
    simp only [lengthLoop, ih, List.length_cons]
    congr 2 <;> omega

def powerLoop : ℕ → ℕ → ℕ → (ℕ × ℕ) × ℕ
  | 0, value, work => ((value, work+1), 8)
  | k+1, value, work => powerLoop k (2*value) (work+3)

theorem powerLoop_formula (k value work : ℕ) :
    powerLoop k value work = ((value*2^k, work+3*k+1), 8) := by
  induction k generalizing value work with
  | zero => simp only [powerLoop, pow_zero, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
  | succ k ih =>
    simp only [powerLoop, ih, pow_succ]
    congr 2 <;> ring

def chooseAcc (n : ℕ) : ℕ → CountedBinomial.State → CountedBinomial.State × ℕ
  | 0, s => (s, 16)
  | k+1, s => chooseAcc n k (CountedBinomial.step n s)

theorem chooseAcc_value (n k : ℕ) (s : CountedBinomial.State) :
    (chooseAcc n k s).1 = CountedBinomial.runAcc n k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _

theorem chooseAcc_cells (n k : ℕ) (s : CountedBinomial.State) :
    (chooseAcc n k s).2 ≤ 16 := by
  induction k generalizing s with
  | zero => exact le_rfl
  | succ k ih => exact ih _

def choose (n k : ℕ) : CountedBinomial.State × ℕ :=
  if k ≤ n then chooseAcc n k CountedBinomial.initial else (⟨k, 0, 0⟩, 16)

theorem choose_value (n k : ℕ) : (choose n k).1 = CountedBinomial.run n k := by
  simp only [choose, CountedBinomial.run]
  split
  · exact chooseAcc_value _ _ _
  · rfl

theorem choose_cells (n k : ℕ) : (choose n k).2 ≤ 16 := by
  rw [choose]
  split
  · exact chooseAcc_cells _ _ _
  · exact le_rfl

def leaf (L : RepresentationLeaf (Fin n)) : (ℕ × ℕ) × ℕ :=
  let ts := FiniteSetCells.domain L.top
  let ms := FiniteSetCells.domain L.mixer
  let bs := FiniteSetCells.domain L.background
  let nt := lengthLoop ts.1.1 0 0
  let nm := lengthLoop ms.1.1 0 0
  let nb := lengthLoop bs.1.1 0 0
  let a := choose nt.1.1 L.topCount
  let b := choose nm.1.1 L.localCount
  let c := powerLoop nb.1.1 1 0
  ((a.1.value*b.1.value*c.1.1,
      ts.1.2+ms.1.2+bs.1.2+nt.1.2+nm.1.2+nb.1.2+
        8*a.1.steps+8*b.1.steps+c.1.2+12),
    ts.2+ms.2+bs.2+nt.2+nm.2+nb.2+a.2+b.2+c.2+6*n+32)

theorem leaf_value (L : RepresentationLeaf (Fin n)) :
    (leaf L).1 = ComputedParentFuels.leaf L := by
  rw [ComputedParentFuels.leaf_formula]
  simp only [leaf, lengthLoop_formula, powerLoop_formula, FiniteSetCells.domain_value,
    RepresentationLeaf.domainSort_length, choose_value, CountedBinomial.run_value,
    Nat.zero_add, Nat.one_mul]

theorem leaf_cells (L : RepresentationLeaf (Fin n)) :
    (leaf L).2 ≤ 256*(n+1)^2 := by
  have ht := FiniteSetCells.domain_cells L.top
  have hm := FiniteSetCells.domain_cells L.mixer
  have hb := FiniteSetCells.domain_cells L.background
  have ha := choose_cells (lengthLoop (FiniteSetCells.domain L.top).1.1 0 0).1.1 L.topCount
  have hbb := choose_cells (lengthLoop (FiniteSetCells.domain L.mixer).1.1 0 0).1.1 L.localCount
  simp only [lengthLoop_formula, Nat.zero_add] at ha hbb
  simp only [leaf, lengthLoop_formula, powerLoop_formula, Nat.zero_add]
  nlinarith only [ht, hm, hb, ha, hbb, Nat.zero_le n]

def run (D : RepresentationParentData n) : (ComputedParentFuels.Values × ℕ) × ℕ :=
  let a := leaf (D.leaves 0)
  let b := leaf (D.leaves 1)
  let c := leaf (D.leaves 2)
  let d := leaf (D.leaves 3)
  let f := a.1.1*b.1.1
  let g := c.1.1*d.1.1
  ((⟨f, g, f+g+1⟩, a.1.2+b.1.2+c.1.2+d.1.2+7), a.2+b.2+c.2+d.2+32)

theorem run_value (D : RepresentationParentData n) :
    (run D).1 = ComputedParentFuels.run D := by
  simp only [run, leaf_value, ComputedParentFuels.run]

theorem run_cells (D : RepresentationParentData n) (hn : 10000 ≤ n) :
    (run D).2 ≤ inputScale D.input^3 := by
  have h₀ := leaf_cells (D.leaves 0)
  have h₁ := leaf_cells (D.leaves 1)
  have h₂ := leaf_cells (D.leaves 2)
  have h₃ := leaf_cells (D.leaves 3)
  have hu : n+1 ≤ inputScale D.input := by unfold inputScale; omega
  have hu0 : 10000 ≤ inputScale D.input := by omega
  have hq := Nat.pow_le_pow_left hu 2
  have hpos : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hmajor : 1056*inputScale D.input^2 ≤ inputScale D.input^3 := by
    calc
      _ ≤ inputScale D.input*inputScale D.input^2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  change _+_+_+_+32 ≤ _
  nlinarith only [h₀, h₁, h₂, h₃, hq, hpos, hmajor]

end LowSpaceSubsetSum.ComputedFuelCells

end OAI
