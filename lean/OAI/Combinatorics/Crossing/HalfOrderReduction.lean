import OAI.Combinatorics.Crossing.DetectorAnnihilation
import OAI.Combinatorics.Crossing.DetectorRelabeling
import OAI.Combinatorics.Crossing.OrderedNodeIndices

namespace OAI

noncomputable section
namespace Zarankiewicz

variable {ι : Type*}

def strictLowerMatrix (α : Type*) [LinearOrder α] : Matrix α α ℝ :=
  fun p q => if q < p then 1 else 0

theorem halfOrder_decomposition [LinearOrder ι] :
    halfOrderMatrix ι = Matrix.of (fun (_ _ : ι) => (1/2 : ℝ)) - strictLowerMatrix ι -
      Matrix.diagonal (fun _ => (1/2 : ℝ)) := by
  funext p q
  rcases lt_trichotomy p q with h | rfl | h
  · norm_num [halfOrderMatrix, strictLowerMatrix, Matrix.diagonal_apply, Matrix.of_apply, ne_of_lt h,
      h, not_lt.mpr h.le]
  · norm_num [halfOrderMatrix, strictLowerMatrix, Matrix.diagonal_apply]
  · norm_num [halfOrderMatrix, strictLowerMatrix, Matrix.diagonal_apply, Matrix.of_apply, (ne_of_lt h).symm,
      h, not_lt.mpr h.le]

def triangleCoefficient (s : ℕ) (p q : OrderedNode s) : ℝ :=
  if p.val ≤ s+1 then (if q < p then 1 else 0) else (if p < q then -1 else 0)

def rowCut (s : ℕ) (p : OrderedNode s) : ℝ := if s+1 < p.val then 1 else 0

theorem lower_triangle_decomposition (s : ℕ) :
    strictLowerMatrix (OrderedNode s) = Matrix.of (fun p q => triangleCoefficient s p q) +
      Matrix.of (fun p (_ : OrderedNode s) => rowCut s p) + Matrix.diagonal (fun p => -rowCut s p) := by
  funext p q
  rcases lt_trichotomy p q with h | rfl | h
  · simp [strictLowerMatrix, triangleCoefficient, rowCut, Matrix.of_apply,
      h, not_lt.mpr h.le, ne_of_lt h]
    split_ifs <;> norm_num <;> omega
  · simp [strictLowerMatrix, triangleCoefficient, rowCut]
  · simp [strictLowerMatrix, triangleCoefficient, rowCut, Matrix.of_apply,
      h, not_lt.mpr h.le, (ne_of_lt h).symm]
    split_ifs <;> norm_num <;> omega

theorem triangleCoefficient_nat_nonzero (s p q : ℕ) (hp : 1 ≤ p ∧ p ≤ 2*s+1)
    (hq : 1 ≤ q ∧ q ≤ 2*s+1) :
    (if p ≤ s+1 then (if q < p then (1 : ℝ) else 0)
      else (if p < q then -1 else 0)) ≠ 0 ↔ (p,q) ∈ twoTriangle s := by
  obtain ⟨hp_lower, hp_upper⟩ := hp
  rw [mem_twoTriangle]
  split_ifs <;> norm_num <;> omega

theorem triangleCoefficient_ne_zero_iff (s : ℕ) (p q : OrderedNode s) :
    triangleCoefficient s p q ≠ 0 ↔ (p.val,q.val) ∈ twoTriangle s :=
  triangleCoefficient_nat_nonzero s p.val q.val (Finset.mem_Icc.mp p.property)
    (Finset.mem_Icc.mp q.property)

theorem rankDetector_halfOrder_reduction (s : ℕ) (node : OrderedNode s → ℝ)
    (hn : Function.Injective node) :
    rankDetector s node (halfOrderMatrix (OrderedNode s)) =
      -rankDetector s node (Matrix.of (fun p q => triangleCoefficient s p q)) := by
  have hrow := rankDetector_additive s node hn (card_orderedNode s) (rowCut s) (fun _ => 0)
  simp only [add_zero] at hrow
  change rankDetector s node (Matrix.of (fun p (_ : OrderedNode s) => rowCut s p)) = 0 at hrow
  have hconst := rankDetector_additive s node hn (card_orderedNode s) (fun _ => (1/2 : ℝ)) (fun _ => 0)
  simp only [add_zero] at hconst
  change rankDetector s node (Matrix.of (fun (_ _ : OrderedNode s) => (1/2 : ℝ))) = 0 at hconst
  have hlower : rankDetector s node (strictLowerMatrix (OrderedNode s)) =
      rankDetector s node (Matrix.of (fun p q => triangleCoefficient s p q)) := by
    rw [lower_triangle_decomposition, map_add, map_add, hrow, rankDetector_diagonal, add_zero, add_zero]
  rw [halfOrder_decomposition, map_sub, map_sub, hconst, hlower, rankDetector_diagonal,
    zero_sub, sub_zero]

end Zarankiewicz

end

end OAI
