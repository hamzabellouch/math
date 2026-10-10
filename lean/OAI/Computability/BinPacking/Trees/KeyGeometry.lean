import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.Packing.CoordinateOrder

namespace OAI

namespace BinPackingGap.Geometry

def keyExpression (m R D L : ℕ) (row key : Position m R) (edge : Fin m)
    (nonpermit short : Bool) : ℚ :=
  baseline m R row - baseline m R key + beta m R edge - beta m R key.1 +
    delta m R D L * ((if nonpermit then 1 else 0) - (if short then 1 else 0))

theorem keyExpression_eq_coordinates (m R D L : ℕ) (row key : Position m R)
    (edge : Fin m) (nonpermit short : Bool) :
    keyExpression m R D L row key edge nonpermit short =
      (baseline m R row - if short then delta m R D L else 0) +
      (-baseline m R key - beta m R key.1) +
      (beta m R edge + if nonpermit then delta m R D L else 0) + 0 + 0 := by
  cases nonpermit <;> cases short <;> simp [keyExpression] <;> ring

theorem key_perturbation_lower (m R D L : ℕ) (nonpermit short : Bool) :
    -delta m R D L ≤
      delta m R D L * ((if nonpermit then 1 else 0) - (if short then 1 else 0)) := by
  have hd := delta_nonneg m R D L
  cases nonpermit <;> cases short <;> simp_all

theorem keyExpression_pos_of_later_row {m R D L : ℕ}
    {row key : Position m R} (edge : Fin m) (nonpermit short : Bool)
    (hlater : posLT key row) :
    0 < keyExpression m R D L row key edge nonpermit short := by
  have hg := gap_pos m R
  have hd := delta_lt_gap m R D L
  have hjump := mul_le_mul_of_nonneg_left (heightCode_jump hlater) (le_of_lt hg)
  have hedge := mul_nonneg (le_of_lt hg) (theta_nonneg R edge)
  have hpert := key_perturbation_lower m R D L nonpermit short
  dsimp [keyExpression, baseline, beta]
  nlinarith

theorem keyExpression_pos_of_later_edge {m R D L : ℕ}
    (row key : Position m R) {edge : Fin m} (nonpermit short : Bool)
    (hlater : key.1 < edge) :
    0 < keyExpression m R D L row key edge nonpermit short := by
  have hg := gap_pos m R
  have hd := delta_lt_gap m R D L
  have hjump := mul_le_mul_of_nonneg_left
    (theta_jump_ge_heightCode (R := R) hlater) (le_of_lt hg)
  have hrow := mul_nonneg (le_of_lt hg) (heightCode_nonneg R row)
  have hpert := key_perturbation_lower m R D L nonpermit short
  dsimp [keyExpression, baseline, beta]
  nlinarith

theorem row_order_of_key_feasible {m R D L : ℕ}
    {row key : Position m R} {edge : Fin m} {nonpermit short : Bool}
    (h : keyExpression m R D L row key edge nonpermit short ≤ 0) :
    posLE row key := by
  apply posLE_iff_not_posLT.mpr
  intro hlater
  exact (not_lt_of_ge h) (keyExpression_pos_of_later_row edge nonpermit short hlater)

theorem edge_order_of_key_feasible {m R D L : ℕ}
    {row key : Position m R} {edge : Fin m} {nonpermit short : Bool}
    (h : keyExpression m R D L row key edge nonpermit short ≤ 0) :
    edge ≤ key.1 := by
  by_contra hnot
  exact (not_lt_of_ge h)
    (keyExpression_pos_of_later_edge row key nonpermit short (lt_of_not_ge hnot))

theorem keyExpression_exact_position_edge (m R D L : ℕ)
    (key : Position m R) (nonpermit short : Bool) :
    keyExpression m R D L key key key.1 nonpermit short =
      delta m R D L * ((if nonpermit then 1 else 0) - (if short then 1 else 0)) := by
  simp [keyExpression]

theorem short_exact_key_feasible (m R D L : ℕ) (key : Position m R)
    (nonpermit : Bool) :
    keyExpression m R D L key key key.1 nonpermit true ≤ 0 := by
  rw [keyExpression_exact_position_edge]
  have hd := delta_nonneg m R D L
  cases nonpermit <;> simp_all

theorem long_exact_key_feasible_iff (m R D L : ℕ) (key : Position m R)
    (nonpermit : Bool) :
    keyExpression m R D L key key key.1 nonpermit false ≤ 0 ↔ nonpermit = false := by
  rw [keyExpression_exact_position_edge]
  have hd := delta_pos m R D L
  cases nonpermit <;> simp_all

theorem exact_long_key_resource {m R D L : ℕ}
    (key : Position m R) (edge : Fin m) (nonpermit : Bool)
    (h : keyExpression m R D L key key edge nonpermit false ≤ 0) :
    edge < key.1 ∨ (edge = key.1 ∧ nonpermit = false) := by
  have he := edge_order_of_key_feasible h
  rcases lt_or_eq_of_le he with hlt | heq
  · exact Or.inl hlt
  · right
    refine ⟨heq, ?_⟩
    subst edge
    exact (long_exact_key_feasible_iff m R D L key nonpermit).mp h

end BinPackingGap.Geometry

end OAI
