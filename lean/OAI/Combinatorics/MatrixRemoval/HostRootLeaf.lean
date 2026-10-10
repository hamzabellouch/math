import OAI.Combinatorics.MatrixRemoval.Host

namespace OAI

/-! Root bits and shared-leaf entries of the exact canonical construction. -/

namespace Problem348.Construction

/-- At the root, all uniform coordinates name node zero. -/
theorem node_eq_zero_of_depth_zero {h : ℕ} (v : VariablePosition h)
    (hv : depth v = 0) : node v = 0 := by
  unfold node
  rw [hv, Nat.sub_zero]
  exact Nat.div_eq_of_lt v.2.isLt

/-- The even class zero is the plus root. -/
@[simp] theorem depth_root_plus {h : ℕ} (x : Fin (2 ^ h)) :
    depth ((0 : Fin (2 * h + 1)), x) = 0 := by
  simp [depth]

@[simp] theorem plus_root_plus {h : ℕ} (x : Fin (2 ^ h)) :
    plus ((0 : Fin (2 * h + 1)), x) = true := by
  simp [plus]

/-- All entries between the two plus-root blocks are one. -/
theorem variableEntry_root_plus {h : ℕ} (x y : Fin (2 ^ h)) :
    variableEntry ((0 : Fin (2 * h + 1)), x)
      ((0 : Fin (2 * h + 1)), y) = true := by
  have hx := node_eq_zero_of_depth_zero ((0 : Fin (2 * h + 1)), x)
    (depth_root_plus x)
  have hy := node_eq_zero_of_depth_zero ((0 : Fin (2 * h + 1)), y)
    (depth_root_plus y)
  simp [variableEntry, hx, hy]

/-- Class one is the minus root when the tree has positive height. -/
@[simp] theorem depth_root_minus {h : ℕ} (hh : 1 ≤ h) (x : Fin (2 ^ h)) :
    depth ((⟨1, by omega⟩ : Fin (2 * h + 1)), x) = 0 := by
  simp [depth]

@[simp] theorem plus_root_minus {h : ℕ} (hh : 1 ≤ h) (x : Fin (2 ^ h)) :
    plus ((⟨1, by omega⟩ : Fin (2 * h + 1)), x) = false := by
  simp [plus]

/-- All entries between the minus-root blocks are zero. -/
theorem variableEntry_root_minus {h : ℕ} (hh : 1 ≤ h) (x y : Fin (2 ^ h)) :
    variableEntry ((⟨1, by omega⟩ : Fin (2 * h + 1)), x)
      ((⟨1, by omega⟩ : Fin (2 * h + 1)), y) = false := by
  have hx := node_eq_zero_of_depth_zero
    ((⟨1, by omega⟩ : Fin (2 * h + 1)), x) (depth_root_minus hh x)
  have hy := node_eq_zero_of_depth_zero
    ((⟨1, by omega⟩ : Fin (2 * h + 1)), y) (depth_root_minus hh y)
  simp [variableEntry, depth, plus, hx, hy, show 0 ≠ h by omega]

/-- The last class is the single shared leaf class. -/
@[simp] theorem depth_shared_leaf {h : ℕ} (x : Fin (2 ^ h)) :
    depth (Fin.last (2 * h), x) = h := by
  simp [depth]

@[simp] theorem node_shared_leaf {h : ℕ} (x : Fin (2 ^ h)) :
    node (Fin.last (2 * h), x) = x.val := by
  simp [node]

/-- Entry values at shared leaves, including the minus diagonal. -/
theorem variableEntry_shared_leaf {h : ℕ} (x y : Fin (2 ^ h)) :
    variableEntry (Fin.last (2 * h), x) (Fin.last (2 * h), y) =
      decide (x.val ≤ y.val) := by
  simp [variableEntry]

/-- Exact unchanged plus root bit on the full host. -/
theorem host_root_plus {h : ℕ} (x y : Fin (2 ^ h)) :
    host (Sum.inr (Sum.inl ((0 : Fin (2 * h + 1)), x)))
      (Sum.inr (Sum.inl ((0 : Fin (2 * h + 1)), y))) = true :=
  variableEntry_root_plus x y

/-- Exact unchanged minus root bit on the full host. -/
theorem host_root_minus {h : ℕ} (hh : 1 ≤ h) (x y : Fin (2 ^ h)) :
    host (Sum.inr (Sum.inl ((⟨1, by omega⟩ : Fin (2 * h + 1)), x)))
      (Sum.inr (Sum.inl ((⟨1, by omega⟩ : Fin (2 * h + 1)), y))) = false :=
  variableEntry_root_minus hh x y

/-- The shared-leaf diagonal consists of ones. -/
theorem host_shared_leaf_diagonal {h : ℕ} (x : Fin (2 ^ h)) :
    host (Sum.inr (Sum.inl (Fin.last (2 * h), x)))
      (Sum.inr (Sum.inl (Fin.last (2 * h), x))) = true := by
  simp [host, variableEntry_shared_leaf]

/-- Constructor-free form of the positive root entry. -/
theorem variableEntry_root_plus_of_atLevel {h : ℕ} (hh : 1 ≤ h)
    (r c : VariablePosition h) (hr : AtLevel 0 true r) (hc : AtLevel 0 true c) :
    variableEntry r c = true := by
  have hrp : plus r = true := hr.2.resolve_left (by omega)
  have hcp : plus c = true := hc.2.resolve_left (by omega)
  have hrn := node_eq_zero_of_depth_zero r hr.1
  have hcn := node_eq_zero_of_depth_zero c hc.1
  simp [variableEntry, hr.1, hc.1, hrp, hcp, hrn, hcn]

/-- Constructor-free form of the negative root entry. -/
theorem variableEntry_root_minus_of_atLevel {h : ℕ} (hh : 1 ≤ h)
    (r c : VariablePosition h) (hr : AtLevel 0 false r) (hc : AtLevel 0 false c) :
    variableEntry r c = false := by
  have hrp : plus r = false := hr.2.resolve_left (by omega)
  have hcp : plus c = false := hc.2.resolve_left (by omega)
  have hrn := node_eq_zero_of_depth_zero r hr.1
  have hcn := node_eq_zero_of_depth_zero c hc.1
  simp [variableEntry, hr.1, hc.1, hrp, hcp, hrn, hcn, show 0 ≠ h by omega]

/-- Every shared-leaf node is its coordinate. -/
theorem node_eq_coordinate_of_leaf {h : ℕ} (r : VariablePosition h)
    (hr : depth r = h) : node r = r.2.val := by
  simp [node, hr]

/-- Constructor-free shared-leaf threshold formula. -/
theorem variableEntry_leaf_of_depth {h : ℕ} (r c : VariablePosition h)
    (hr : depth r = h) (hc : depth c = h) :
    variableEntry r c = decide (r.2.val ≤ c.2.val) := by
  simp [variableEntry, hr, hc, node_eq_coordinate_of_leaf r hr,
    node_eq_coordinate_of_leaf c hc]

end Problem348.Construction

end OAI
