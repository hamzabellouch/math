import OAI.Combinatorics.MatrixRemoval.Model

namespace OAI

/-!
The raw finite host; row and column orders are supplied separately.
The second coordinate in a variable class is uniform on `Fin (2^h)`;
its quotient by the block size is the node index.
-/
noncomputable section
namespace Problem348.Construction

abbrev VariablePosition (h : ℕ) := Fin (2 * h + 1) × Fin (2 ^ h)
abbrev AnchorPosition (h : ℕ) := Fin (6 * h) × Fin 64 × Fin (2 ^ h)
abbrev Position (h : ℕ) := AnchorPosition h ⊕ (VariablePosition h ⊕ Fin (2 ^ h))
abbrev Mode (h : ℕ) := Fin (6 * h)

def depth {h : ℕ} (x : VariablePosition h) : ℕ := x.1.val / 2
def node {h : ℕ} (x : VariablePosition h) : ℕ := x.2.val / 2 ^ (h - depth x)
def plus {h : ℕ} (x : VariablePosition h) : Bool := decide (x.1.val % 2 = 0)
def level {h : ℕ} (t : Mode h) : ℕ := t.val / 6 + 1
def kind {h : ℕ} (t : Mode h) : ℕ := t.val % 6

def AtLevel {h : ℕ} (i : ℕ) (s : Bool) (x : VariablePosition h) : Prop :=
  depth x = i ∧ (i = h ∨ plus x = s)

def rowRole {h : ℕ} (t : Mode h) (j : Fin 2) (x : Position h) : Prop :=
  match x with
  | Sum.inl _ => False
  | Sum.inr (Sum.inr _) => 2 ≤ kind t ∧ j.val = 1
  | Sum.inr (Sum.inl v) =>
    if kind t = 0 then
      AtLevel (if j.val = 0 then level t else level t - 1) true v
    else if kind t = 1 then
      AtLevel (if j.val = 0 then level t - 1 else level t) false v
    else
      j.val = 0 ∧ AtLevel (level t) (decide (kind t < 4)) v ∧
        node v % 2 = (kind t % 2)

def colRole {h : ℕ} (t : Mode h) (j : Fin 2) (x : Position h) : Prop :=
  match x with
  | Sum.inl _ => False
  | Sum.inr (Sum.inr _) => kind t < 2 ∧ j.val = 0
  | Sum.inr (Sum.inl v) =>
    if kind t < 2 then
      j.val = 1 ∧ AtLevel (level t - 1) (decide (kind t = 0)) v
    else if kind t < 4 then
      if j.val = 0 then AtLevel (level t - 1) true v
      else AtLevel (level t) true v ∧ node v % 2 = kind t % 2
    else
      if j.val = 0 then AtLevel (level t) false v ∧ node v % 2 = kind t % 2
      else AtLevel (level t - 1) false v

instance {h : ℕ} (i : ℕ) (s : Bool) (v : VariablePosition h) :
    Decidable (AtLevel i s v) := inferInstanceAs (Decidable (_ ∧ _))
instance {h : ℕ} (t : Mode h) (j : Fin 2) (x : Position h) :
    Decidable (rowRole t j x) := by unfold rowRole; split <;> infer_instance
instance {h : ℕ} (t : Mode h) (j : Fin 2) (x : Position h) :
    Decidable (colRole t j x) := by unfold colRole; split <;> infer_instance

def variableEntry {h : ℕ} (r c : VariablePosition h) : Bool :=
  if depth r = depth c then
    if depth r = h then decide (node r ≤ node c)
    else if plus r = plus c then
      if plus r then decide (node r ≤ node c) else decide (node r < node c)
    else false
  else if depth r = depth c + 1 ∧ depth c < h ∧
      (depth r = h ∨ plus r = plus c) then
    if plus c then decide (node r / 2 ≤ node c) else decide (node r / 2 < node c)
  else false

def host {h : ℕ} (r c : Position h) : Bool :=
  match r, c with
  | Sum.inl (t, u, _), Sum.inl (t', v, _) =>
      if t = t' then Problem348.anchor64 u v else false
  | Sum.inl (t, u, _), Sum.inr _ =>
      decide ((u.val = 0 ∧ colRole t 0 c) ∨ (u.val = 1 ∧ colRole t 1 c))
  | Sum.inr _, Sum.inl (t, v, _) =>
      decide ((v.val = 0 ∧ rowRole t 0 r) ∨ (v.val = 1 ∧ rowRole t 1 r))
  | Sum.inr (Sum.inl v), Sum.inr (Sum.inl w) => variableEntry v w
  | Sum.inr _, Sum.inr _ => true

theorem depth_le {h : ℕ} (x : VariablePosition h) : depth x ≤ h := by
  have hx := x.1.isLt
  unfold depth
  omega

theorem level_pos {h : ℕ} (t : Mode h) : 1 ≤ level t := by
  unfold level
  omega

theorem level_le {h : ℕ} (t : Mode h) : level t ≤ h := by
  have ht := t.isLt
  unfold level
  omega

theorem kind_lt {h : ℕ} (t : Mode h) : kind t < 6 := by
  exact Nat.mod_lt _ (by decide)

theorem card_variablePosition (h : ℕ) :
    Fintype.card (VariablePosition h) = (2 * h + 1) * 2 ^ h := by
  simp [VariablePosition]

theorem card_position (h : ℕ) :
    Fintype.card (Position h) = (386 * h + 2) * 2 ^ h := by
  simp only [Position, AnchorPosition, VariablePosition, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin]
  ring

@[simp] theorem host_anchor_same {h : ℕ} (t : Mode h) (u v : Fin 64)
    (x y : Fin (2 ^ h)) :
    host (Sum.inl (t, u, x)) (Sum.inl (t, v, y)) = anchor64 u v := by
  simp [host]

@[simp] theorem host_anchor_different {h : ℕ} (t t' : Mode h) (ht : t ≠ t')
    (u v : Fin 64) (x y : Fin (2 ^ h)) :
    host (Sum.inl (t, u, x)) (Sum.inl (t', v, y)) = false := by
  simp [host, ht]

@[simp] theorem host_variable_variable {h : ℕ} (v w : VariablePosition h) :
    host (Sum.inr (Sum.inl v)) (Sum.inr (Sum.inl w)) = variableEntry v w := rfl

@[simp] theorem host_dummy_variable {h : ℕ} (x : Fin (2 ^ h))
    (v : VariablePosition h) :
    host (Sum.inr (Sum.inr x)) (Sum.inr (Sum.inl v)) = true := rfl

@[simp] theorem host_variable_dummy {h : ℕ} (x : Fin (2 ^ h))
    (v : VariablePosition h) :
    host (Sum.inr (Sum.inl v)) (Sum.inr (Sum.inr x)) = true := rfl

theorem rowRole_disjoint {h : ℕ} (t : Mode h) (x : Position h) :
    ¬ (rowRole t 0 x ∧ rowRole t 1 x) := by
  have hp := level_pos t
  have hk := kind_lt t
  rcases x with a | (v | d)
  · simp [rowRole]
  · interval_cases e : kind t <;>
      simp [rowRole, e, AtLevel] <;> omega
  · simp [rowRole]

theorem colRole_disjoint {h : ℕ} (t : Mode h) (x : Position h) :
    ¬ (colRole t 0 x ∧ colRole t 1 x) := by
  have hp := level_pos t
  have hk := kind_lt t
  rcases x with a | (v | d)
  · simp [colRole]
  · interval_cases e : kind t <;>
      simp [colRole, e, AtLevel] <;> omega
  · simp [colRole]

end Problem348.Construction

end

end OAI
