import OAI.Combinatorics.MatrixRemoval.Host
import OAI.Combinatorics.MatrixRemoval.SampledPath

namespace OAI

/-!
Concrete sampled-path role membership for the canonical host.
The input is one common leaf seed and arbitrary within-class offset seeds.
-/
namespace Problem348.HostSampledPath

open SampledPath

/-- The variable-position sample, injected into the full host axis. -/
def position (h i : ℕ) (hi : i ≤ h) (plus : Bool)
    (z u : Fin (2 ^ h)) : Construction.Position h :=
  Sum.inr (Sum.inl (sample h i hi plus z u))

/-- A sampled dummy position. -/
def dummy (h : ℕ) (u : Fin (2 ^ h)) : Construction.Position h :=
  Sum.inr (Sum.inr u)

@[simp] theorem sample_atLevel (h i : ℕ) (hi : i ≤ h) (s : Bool)
    (z u : Fin (2 ^ h)) : Construction.AtLevel i s (sample h i hi s z u) := by
  constructor
  · exact sample_depth h i hi s z u
  · by_cases heq : i = h
    · exact Or.inl heq
    · right
      cases s <;>
        simp [Construction.plus, sample, classAt, heq]

@[simp] theorem sample_hostNode (h i : ℕ) (hi : i ≤ h) (s : Bool)
    (z u : Fin (2 ^ h)) :
    Construction.node (sample h i hi s z u) = z.val / blockSize h i :=
  sample_node h i hi s z u

@[simp] theorem position_shared_leaf (h : ℕ) (s t : Bool)
    (z u v : Fin (2 ^ h)) :
    position h h le_rfl s z u = position h h le_rfl t z v := by
  exact congrArg (fun p : Construction.VariablePosition h =>
    (Sum.inr (Sum.inl p) : Construction.Position h))
    (sample_shared_leaf h s t z u v)

/-- Encode the mode at the edge from depth `i` to depth `i+1`. -/
def mode {h : ℕ} (i : Fin h) (k : Fin 6) : Construction.Mode h :=
  ⟨6 * i.val + k.val, by have := i.isLt; have := k.isLt; omega⟩

@[simp] theorem mode_level {h : ℕ} (i : Fin h) (k : Fin 6) :
    Construction.level (mode i k) = i.val + 1 := by
  have := k.isLt
  unfold Construction.level mode
  dsimp
  omega

@[simp] theorem mode_kind {h : ℕ} (i : Fin h) (k : Fin 6) :
    Construction.kind (mode i k) = k.val := by
  have := k.isLt
  unfold Construction.kind mode
  dsimp
  omega

def verticalKind : Bool → Fin 6
  | true => 0
  | false => 1

def horizontalKind : Bool → Bool → Fin 6
  | true, false => 2
  | true, true => 3
  | false, false => 4
  | false, true => 5

def vertical {h : ℕ} (i : Fin h) (s : Bool) : Construction.Mode h :=
  mode i (verticalKind s)
def horizontal {h : ℕ} (i : Fin h) (s d : Bool) : Construction.Mode h :=
  mode i (horizontalKind s d)

def parity (n : ℕ) : Bool := decide (n % 2 = 1)

@[simp] theorem parity_eq_false (n : ℕ) : parity n = false ↔ n % 2 = 0 := by
  simp only [parity, decide_eq_false_iff_not]
  omega

@[simp] theorem parity_eq_true (n : ℕ) : parity n = true ↔ n % 2 = 1 := by
  simp [parity]

 theorem vertical_plus_row_first {h : ℕ} (i : Fin h) (z u : Fin (2 ^ h)) :
    Construction.rowRole (vertical i true) 0
      (position h (i.val + 1) (by omega) true z u) := by
  simp [vertical, verticalKind, Construction.rowRole, position]

 theorem vertical_plus_row_second {h : ℕ} (i : Fin h) (z u : Fin (2 ^ h)) :
    Construction.rowRole (vertical i true) 1
      (position h i.val (by omega) true z u) := by
  simp [vertical, verticalKind, Construction.rowRole, position]

 theorem vertical_minus_row_first {h : ℕ} (i : Fin h) (z u : Fin (2 ^ h)) :
    Construction.rowRole (vertical i false) 0
      (position h i.val (by omega) false z u) := by
  simp [vertical, verticalKind, Construction.rowRole, position]

 theorem vertical_minus_row_second {h : ℕ} (i : Fin h) (z u : Fin (2 ^ h)) :
    Construction.rowRole (vertical i false) 1
      (position h (i.val + 1) (by omega) false z u) := by
  simp [vertical, verticalKind, Construction.rowRole, position]

 theorem vertical_col_first {h : ℕ} (i : Fin h) (s : Bool) (u : Fin (2 ^ h)) :
    Construction.colRole (vertical i s) 0 (dummy h u) := by
  cases s <;> simp [vertical, verticalKind, Construction.colRole, dummy]

 theorem vertical_col_second {h : ℕ} (i : Fin h) (s : Bool) (z u : Fin (2 ^ h)) :
    Construction.colRole (vertical i s) 1 (position h i.val (by omega) s z u) := by
  cases s <;> simp [vertical, verticalKind, Construction.colRole, position]

 theorem horizontal_row_second {h : ℕ} (i : Fin h) (s d : Bool)
    (u : Fin (2 ^ h)) : Construction.rowRole (horizontal i s d) 1 (dummy h u) := by
  cases s <;> cases d <;> simp [horizontal, horizontalKind, Construction.rowRole, dummy]

 theorem horizontal_row_first {h : ℕ} (i : Fin h) (s : Bool)
    (z u : Fin (2 ^ h)) :
    Construction.rowRole (horizontal i s (parity (z.val / blockSize h (i.val + 1)))) 0
      (position h (i.val + 1) (by omega) s z u) := by
  have hp := Nat.mod_lt (z.val / blockSize h (i.val + 1)) (by decide : 0 < 2)
  cases s <;> by_cases hd : (z.val / blockSize h (i.val + 1)) % 2 = 1 <;>
    simp_all [horizontal, horizontalKind, Construction.rowRole, position, parity]

 theorem horizontal_plus_col_first {h : ℕ} (i : Fin h) (d : Bool)
    (z u : Fin (2 ^ h)) :
    Construction.colRole (horizontal i true d) 0 (position h i.val (by omega) true z u) := by
  cases d <;> simp [horizontal, horizontalKind, Construction.colRole, position]

 theorem horizontal_plus_col_second {h : ℕ} (i : Fin h) (z u : Fin (2 ^ h)) :
    Construction.colRole (horizontal i true (parity (z.val / blockSize h (i.val + 1)))) 1
      (position h (i.val + 1) (by omega) true z u) := by
  have hp := Nat.mod_lt (z.val / blockSize h (i.val + 1)) (by decide : 0 < 2)
  by_cases hd : (z.val / blockSize h (i.val + 1)) % 2 = 1 <;>
    simp_all [horizontal, horizontalKind, Construction.colRole, position, parity]

 theorem horizontal_minus_col_first {h : ℕ} (i : Fin h) (z u : Fin (2 ^ h)) :
    Construction.colRole (horizontal i false (parity (z.val / blockSize h (i.val + 1)))) 0
      (position h (i.val + 1) (by omega) false z u) := by
  have hp := Nat.mod_lt (z.val / blockSize h (i.val + 1)) (by decide : 0 < 2)
  by_cases hd : (z.val / blockSize h (i.val + 1)) % 2 = 1 <;>
    simp_all [horizontal, horizontalKind, Construction.colRole, position, parity]

 theorem horizontal_minus_col_second {h : ℕ} (i : Fin h) (d : Bool)
    (z u : Fin (2 ^ h)) :
    Construction.colRole (horizontal i false d) 1 (position h i.val (by omega) false z u) := by
  cases d <;> simp [horizontal, horizontalKind, Construction.colRole, position]

end Problem348.HostSampledPath

end OAI
