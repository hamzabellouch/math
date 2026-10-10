import OAI.Combinatorics.MatrixRemoval.Host
import OAI.Combinatorics.MatrixRemoval.ModeLocalization

namespace OAI

/-!
# Vertical-mode localization for the concrete host

The only additional input to the exclusion theorems is the node inequality
provided by the tree order. All entry values and role memberships follow
from the host definitions.
-/

namespace Problem348.Construction

/-- Extend the variable node index to all positions. -/
def positionNode {h : ℕ} : Position h → ℕ
  | Sum.inr (Sum.inl v) => node v
  | _ => 0

@[simp] theorem positionNode_variable {h : ℕ} (v : VariablePosition h) :
    positionNode (Sum.inr (Sum.inl v)) = node v := rfl

theorem variableEntry_same_level {h i : ℕ} {r c : VariablePosition h}
    (s : Bool) (hr : AtLevel i s r) (hc : AtLevel i s c) :
    variableEntry r c =
      if i = h then decide (node r ≤ node c)
      else if s then decide (node r ≤ node c) else decide (node r < node c) := by
  rcases hr with ⟨hrd, hrs⟩
  rcases hc with ⟨hcd, hcs⟩
  by_cases hi : i = h
  · simp [variableEntry, hrd, hcd, hi]
  · have hrp : plus r = s := hrs.resolve_left hi
    have hcp : plus c = s := hcs.resolve_left hi
    simp [variableEntry, hrd, hcd, hi, hrp, hcp]

theorem variableEntry_child_parent {h i : ℕ} {r c : VariablePosition h}
    (s : Bool) (hr : AtLevel (i + 1) s r) (hc : AtLevel i s c) :
    variableEntry r c =
      if s then decide (node r / 2 ≤ node c) else decide (node r / 2 < node c) := by
  rcases hr with ⟨hrd, hrs⟩
  rcases hc with ⟨hcd, hcs⟩
  have hih : i < h := by have := depth_le r; omega
  have hcp : plus c = s := hcs.resolve_left (by omega)
  have hsign : i + 1 = h ∨ plus r = s := hrs
  simp [variableEntry, hrd, hcd, hih, hcp, hsign]

theorem rowRole_vertical_variable {h : ℕ} {t : Mode h} {j : Fin 2}
    {x : Position h} (hk : kind t < 2) (hx : rowRole t j x) :
    ∃ v : VariablePosition h, x = Sum.inr (Sum.inl v) := by
  rcases x with a | (v | d)
  · simp [rowRole] at hx
  · exact ⟨v, rfl⟩
  · simp [rowRole] at hx
    omega

theorem colRole_vertical_first_dummy {h : ℕ} {t : Mode h}
    {x : Position h} (hk : kind t < 2) (hx : colRole t 0 x) :
    ∃ d : Fin (2 ^ h), x = Sum.inr (Sum.inr d) := by
  rcases x with a | (v | d)
  · simp [colRole] at hx
  · simp [colRole, hk] at hx
  · exact ⟨d, rfl⟩

theorem colRole_vertical_second_variable {h : ℕ} {t : Mode h}
    {x : Position h} (_hk : kind t < 2) (hx : colRole t 1 x) :
    ∃ v : VariablePosition h, x = Sum.inr (Sum.inl v) := by
  rcases x with a | (v | d)
  · simp [colRole] at hx
  · exact ⟨v, rfl⟩
  · simp [colRole] at hx

/-- An actual vertical plus mode of the host cannot contain the body. -/
theorem host_vertical_plus_not_body {h : ℕ} {t : Mode h}
    (hk : kind t = 0) {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (horder : positionNode r₀ / 2 ≤ positionNode r₁) :
    ¬ ModeLocalization.IsP (host r₀ c₀) (host r₀ c₁)
      (host r₁ c₀) (host r₁ c₁) := by
  have hkt : kind t < 2 := by omega
  obtain ⟨x, rfl⟩ := rowRole_vertical_variable hkt hr₀
  obtain ⟨y, rfl⟩ := rowRole_vertical_variable hkt hr₁
  obtain ⟨d, rfl⟩ := colRole_vertical_first_dummy hkt hc₀
  obtain ⟨z, rfl⟩ := colRole_vertical_second_variable hkt hc₁
  have hx : AtLevel (level t) true x := by simpa [rowRole, hk] using hr₀
  have hy : AtLevel (level t - 1) true y := by simpa [rowRole, hk] using hr₁
  have hz : AtLevel (level t - 1) true z := by simpa [colRole, hk] using hc₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  have hparent := variableEntry_child_parent true (hl ▸ hx) hz
  have hsame := variableEntry_same_level true hy hz
  have hnotleaf : level t - 1 ≠ h := by
    have := level_le t
    have := level_pos t
    omega
  simpa [host, hparent, hsame, hnotleaf, positionNode] using
    ModeLocalization.vPlus_not_isP (node x) (node y) (node z) horder

/-- An actual vertical minus mode of the host cannot contain the body. -/
theorem host_vertical_minus_not_body {h : ℕ} {t : Mode h}
    (hk : kind t = 1) {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (horder : positionNode r₀ ≤ positionNode r₁ / 2) :
    ¬ ModeLocalization.IsP (host r₀ c₀) (host r₀ c₁)
      (host r₁ c₀) (host r₁ c₁) := by
  have hkt : kind t < 2 := by omega
  obtain ⟨x, rfl⟩ := rowRole_vertical_variable hkt hr₀
  obtain ⟨y, rfl⟩ := rowRole_vertical_variable hkt hr₁
  obtain ⟨d, rfl⟩ := colRole_vertical_first_dummy hkt hc₀
  obtain ⟨z, rfl⟩ := colRole_vertical_second_variable hkt hc₁
  have hx : AtLevel (level t - 1) false x := by simpa [rowRole, hk] using hr₀
  have hy : AtLevel (level t) false y := by simpa [rowRole, hk] using hr₁
  have hz : AtLevel (level t - 1) false z := by simpa [colRole, hk] using hc₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  have hparent := variableEntry_child_parent false (hl ▸ hy) hz
  have hsame := variableEntry_same_level false hx hz
  have hnotleaf : level t - 1 ≠ h := by
    have := level_le t
    have := level_pos t
    omega
  simpa [host, hparent, hsame, hnotleaf, positionNode] using
    ModeLocalization.vMinus_not_isP (node y) (node x) (node z) horder

end Problem348.Construction

end OAI
