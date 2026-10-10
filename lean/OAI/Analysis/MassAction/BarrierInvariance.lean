import OAI.Analysis.MassAction.BarrierGeometry
import OAI.Analysis.MassAction.BarrierTrapping
import OAI.Analysis.MassAction.CompactContinuation

namespace OAI

noncomputable section

open Set

namespace Problem326.BarrierConstruction

namespace AffineBarrierData

variable {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
  {x₀ : Fin d → ℝ}

/-- The exact forward-invariance predicate follows from the constructed barrier,
with no separate global-solvability or regularity assumption. -/
theorem isForwardInvariant (A : AffineBarrierData N κ x₀) :
    Problem326.IsForwardInvariant N κ A.plateau := by
  classical
  let s : Finset (Fin A.n) := Finset.univ
  have hs : s.Nonempty := ⟨A.constant_branch, Finset.mem_univ _⟩
  let F := Barrier.affineMinimum s hs A.slope A.offset
  let M := A.offset A.constant_branch
  have hceil : ∀ x, F x ≤ M := by
    intro x
    dsimp only [F, M, Barrier.affineMinimum]
    have hi := Finset.inf'_le (fun j => dot (A.slope j) x + A.offset j)
      (show A.constant_branch ∈ s from Finset.mem_univ _)
    simpa only [A.slope_constant, dot, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add] using hi
  have hmem : ∀ x, x ∈ A.plateau ↔ F x = M := by
    intro x
    constructor
    · intro hx
      apply le_antisymm (hceil x)
      exact Finset.le_inf' hs _ (fun j _ => hx j)
    · intro hx j
      have hi := Finset.inf'_le (fun k => dot (A.slope k) x + A.offset k)
        (show j ∈ s from Finset.mem_univ _)
      change F x ≤ dot (A.slope j) x + A.offset j at hi
      simpa only [hx] using hi
  apply massAction_isForwardInvariant_of_compact_trapping A.isCompact_plateau
  intro z hz T x hT hx t ht
  have hboundary : ∀ y ∈ frontier A.box, F y ≠ M := by
    intro y hy hF
    exact A.constant_not_active_on_frontier hy
      ((A.mem_plateau_iff_active y).mp ((hmem y).mpr hF))
  have hactive : ∀ y ∈ A.box, ∀ j ∈ s,
      dot (A.slope j) y + A.offset j = F y →
      0 ≤ dot (A.slope j) (massAction N κ y) := by
    intro y hy j hj hjF
    apply A.inward_on_box hy
    intro k
    rw [hjF]
    exact Finset.inf'_le _ (show k ∈ s from Finset.mem_univ _)
  have htrap := Barrier.forward_solution_trapped s hs A.slope A.offset
    hT A.isClosed_box hceil hboundary hactive hx
    (A.plateau_subset_interior_box hz) ((hmem z).mp hz)
  exact (hmem (x t)).mpr (htrap ht).2

end AffineBarrierData

/-- Uniform arbitrary-tolerance affine approximation gives a compact convex
forward-invariant polytope with extension of every finite solution segment. -/
theorem compact_convex_invariant_polytope_of_uniform {d : ℕ}
    (happroximation : UniformAffineApproximation d)
    (N : ReactionNetwork d) (κ : Reaction N → ℝ)
    (hweak : WeaklyReversible N) (hκ : ∀ e, 0 < κ e)
    (x₀ : Fin d → ℝ) (hx₀ : PositiveState x₀) :
    ∃ K : Set (Fin d → ℝ), IsCompact K ∧ Convex ℝ K ∧ IsFinitePolyhedron K ∧
      x₀ ∈ K ∧ K ⊆ {x | PositiveState x} ∧ IsForwardInvariant N κ K := by
  obtain ⟨A⟩ := exists_affineBarrierData happroximation N κ hweak hκ x₀ hx₀
  obtain ⟨hc, hv, hp, hx, hpos⟩ := A.geometric_properties
  exact ⟨A.plateau, hc, hv, hp, hx, hpos, A.isForwardInvariant⟩

end Problem326.BarrierConstruction

end

end OAI
