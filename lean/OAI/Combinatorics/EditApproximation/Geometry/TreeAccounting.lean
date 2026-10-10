import Mathlib
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Finite comparison-tree accounting

A complete tree is indexed by its physical depth and child labels. Terminal
comparison costs may be carried forward, with zero costs in the other child
slots. The identities apply to that representation without any probability
or sampling hypothesis.
-/

namespace EditApproximation

open Finset

/-- Labeled nodes of a complete `M`-ary tree at one physical depth. -/




theorem tree_layer_sum {M d : ℕ} (weight : TreeLayer M (d + 1) → ℝ) :
    (∑ node : TreeLayer M d, ∑ child : Fin M, weight (node, child)) =
      ∑ node : TreeLayer M (d + 1), weight node := by
  exact (Fintype.sum_prod_type weight).symm

/-- Mass/energy differences cancel exactly between successive frontiers. -/
theorem tree_frontier_telescope (M J : ℕ)
    (weight : (d : ℕ) → TreeLayer M d → ℝ) :
    (∑ d ∈ range J, ∑ node : TreeLayer M d,
      (weight d node - ∑ child : Fin M, weight (d + 1) (node, child))) =
        weight 0 PUnit.unit - ∑ node : TreeLayer M J, weight J node := by
  have hstep (d : ℕ) : (∑ node : TreeLayer M d,
      (weight d node - ∑ child : Fin M, weight (d + 1) (node, child))) =
        (∑ node : TreeLayer M d, weight d node) -
          (∑ node : TreeLayer M (d + 1), weight (d + 1) node) := by
    rw [sum_sub_distrib, tree_layer_sum]
  simp_rw [hstep]
  induction J with
  | zero =>
    let : Unique (TreeLayer M 0) := ⟨⟨PUnit.unit⟩, fun a => by cases a; rfl⟩
    rw [sum_range_zero, Fintype.sum_unique]
    exact (sub_self _).symm
  | succ J ih =>
    rw [sum_range_succ, ih]
    ring

/-- The explicit small-growth bound used for the comparison frontiers. -/
theorem small_growth_pow {x : ℝ} (n : ℕ) (hx : 0 ≤ x)
    (hsmall : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n ≤ 1 + 2 * n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (n : ℝ) * x ≤ 1 / 2 := by
      push_cast at hsmall
      nlinarith
    have hprev := mul_le_mul_of_nonneg_right (ih hn) (by positivity : 0 ≤ 1 + x)
    rw [pow_succ]
    apply hprev.trans
    push_cast
    have hprod : 0 ≤ x * (1 - 2 * n * x) := by
      apply mul_nonneg hx
      nlinarith
    nlinarith

/-- The final scalar summation of the local curvature/energy estimates.
The conservation identities are supplied by `tree_frontier_telescope` for
the comparison masses and energies. -/
theorem curvature_total_from_telescope {ι : Type*} (nodes : Finset ι)
    (curvature discrepancy massDifference movement slack energyDifference : ι → ℝ)
    (D rootMass terminalMass : ℝ)
    (hroot : 0 ≤ rootMass) (hterminal : terminalMass ≤ 2 * D)
    (hconservation : (∑ v ∈ nodes, massDifference v) = rootMass - terminalMass)
    (henergy : (∑ v ∈ nodes, energyDifference v) ≤ 2 * D)
    (hdiscrepancy : ∀ v ∈ nodes, 0 ≤ discrepancy v)
    (hslackNonneg : ∀ v ∈ nodes, 0 ≤ slack v)
    (hslack : ∀ v ∈ nodes, massDifference v + discrepancy v ≤ slack v)
    (hcurvature : ∀ v ∈ nodes, curvature v ≤ energyDifference v + 3 * movement v +
      2 * max (-massDifference v) 0) :
    (∑ v ∈ nodes, (curvature v + discrepancy v)) ≤
      8 * D + 3 * (∑ v ∈ nodes, movement v) + 4 * (∑ v ∈ nodes, slack v) := by
  have hpositive (v : ι) (hv : v ∈ nodes) : max (massDifference v) 0 ≤ slack v := by
    apply max_le
    · linarith [hslack v hv, hdiscrepancy v hv]
    · exact hslackNonneg v hv
  have hidentity : (∑ v ∈ nodes, max (-massDifference v) 0) =
      (∑ v ∈ nodes, max (massDifference v) 0) - rootMass + terminalMass := by
    have hpoint (v : ι) : max (-massDifference v) 0 =
        max (massDifference v) 0 - massDifference v := by
      by_cases h : 0 ≤ massDifference v
      · rw [max_eq_left h, max_eq_right (by linarith : -massDifference v ≤ 0)]
        ring
      · rw [max_eq_right (by linarith : massDifference v ≤ 0),
          max_eq_left (by linarith : 0 ≤ -massDifference v)]
        ring
    simp_rw [hpoint]
    rw [sum_sub_distrib, hconservation]
    ring
  have hnegative : (∑ v ∈ nodes, max (-massDifference v) 0) ≤
      (∑ v ∈ nodes, slack v) + 2 * D := by
    rw [hidentity]
    have hsum := sum_le_sum hpositive
    linarith
  have hG : (∑ v ∈ nodes, discrepancy v) ≤
      (∑ v ∈ nodes, max (-massDifference v) 0) + (∑ v ∈ nodes, slack v) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro v hv
    have hminus := le_max_left (-massDifference v) 0
    linarith [hslack v hv]
  have hK : (∑ v ∈ nodes, curvature v) ≤
      (∑ v ∈ nodes, energyDifference v) + 3 * (∑ v ∈ nodes, movement v) +
        2 * (∑ v ∈ nodes, max (-massDifference v) 0) := by
    have hsum := sum_le_sum hcurvature
    simpa only [sum_add_distrib, ← mul_sum] using hsum
  rw [sum_add_distrib]
  linarith

/-- Substituting the endpoint and warmup slack totals gives the
manuscript's stated curvature constant. Here `u=J/P` and `v=J/T`. -/
theorem curvature_total_parameter_bound {total movement slack D F u v : ℝ}
    (hD : 0 ≤ D) (hF : 1 ≤ F) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htotal : total ≤ 8 * D + 3 * movement + 4 * slack)
    (hmove : movement ≤ 4 * u * D)
    (hslack : slack ≤ 512 * F * u * D + 4 * F * v * D) :
    total ≤ 5000 * F * (1 + u + v) * D := by
  have hF0 : 0 ≤ F := by linarith
  have hroot : 8 * D ≤ 5000 * F * D :=
    mul_le_mul_of_nonneg_right (by linarith) hD
  have huc : (2048 * F + 12) * u * D ≤ 5000 * F * u * D :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 2048 * F + 12 ≤ 5000 * F) hu) hD
  have hvc : 16 * F * v * D ≤ 5000 * F * v * D :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by nlinarith : 16 * F ≤ 5000 * F) hv) hD
  nlinarith

/-- Exceptional-node cost uses the total curvature/discrepancy charge;
no count of nodes or independence assumption is needed. -/
theorem bad_node_cost_from_curvature {ι : Type*} (nodes : Finset ι)
    (cost scale curvature discrepancy : ι → ℝ) (ratio totalBound : ℝ)
    (hratio : 0 ≤ ratio)
    (hcost : ∀ i ∈ nodes, cost i ≤ 2 * scale i)
    (hcurvature : ∀ i ∈ nodes, 0 ≤ curvature i)
    (hdiscrepancy : ∀ i ∈ nodes, 0 ≤ discrepancy i)
    (htotal : (∑ i ∈ nodes, (curvature i + discrepancy i)) ≤ totalBound) :
    (∑ i ∈ nodes with scale i < ratio * curvature i ∨ scale i < ratio * discrepancy i,
      cost i) ≤ 2 * ratio * totalBound := by
  classical
  let bad := nodes.filter fun i => scale i < ratio * curvature i ∨
    scale i < ratio * discrepancy i
  have hpoint (i : ι) (hi : i ∈ bad) : cost i ≤ 2 * ratio * (curvature i + discrepancy i) := by
    obtain ⟨hinode, hbad⟩ := mem_filter.mp hi
    have hK := mul_nonneg hratio (hcurvature i hinode)
    have hG := mul_nonneg hratio (hdiscrepancy i hinode)
    rcases hbad with hbad | hbad <;> nlinarith [hcost i hinode]
  have hpartial : (∑ i ∈ bad, (curvature i + discrepancy i)) ≤
      ∑ i ∈ nodes, (curvature i + discrepancy i) := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro i hi _
    exact add_nonneg (hcurvature i hi) (hdiscrepancy i hi)
  have hsum := sum_le_sum hpoint
  rw [← mul_sum] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left (hpartial.trans htotal) (by positivity))

end EditApproximation

end OAI
