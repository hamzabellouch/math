import OAI.Analysis.MassAction.NetworkBarrier
import OAI.Analysis.MassAction.ReciprocalBox
import OAI.Analysis.MassAction.PolyhedronGeometry

namespace OAI

noncomputable section

open Set

namespace Problem326.BarrierConstruction.AffineBarrierData

variable {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
  {x₀ : Fin d → ℝ}

/-- The physical reciprocal box for a constructed affine barrier. -/
def box (A : AffineBarrierData N κ x₀) : Set (Fin d → ℝ) :=
  Icc (fun _ => A.parameter) (fun _ => A.parameter⁻¹)

/-- The plateau selected by the constant branch, as finite affine inequalities. -/
def plateau (A : AffineBarrierData N κ x₀) : Set (Fin d → ℝ) :=
  {x | ∀ j, A.offset A.constant_branch ≤ dot (A.slope j) x + A.offset j}

theorem mem_plateau_iff_active (A : AffineBarrierData N κ x₀) (x : Fin d → ℝ) :
    x ∈ A.plateau ↔ AffineActive A.slope A.offset x A.constant_branch := by
  simp only [plateau, Set.mem_ofPred_eq, AffineActive, A.slope_constant, dot,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

theorem initial_mem_plateau (A : AffineBarrierData N κ x₀) : x₀ ∈ A.plateau :=
  (A.mem_plateau_iff_active x₀).mpr A.initial_active

theorem initial_mem_interior_box (A : AffineBarrierData N κ x₀) :
    x₀ ∈ interior A.box :=
  mem_interior_coordinate_box_iff.mpr A.initial_inside

theorem isCompact_box (A : AffineBarrierData N κ x₀) : IsCompact A.box :=
  isCompact_reciprocal_box A.parameter

theorem isClosed_box (A : AffineBarrierData N κ x₀) : IsClosed A.box := isClosed_Icc

theorem box_subset_positive (A : AffineBarrierData N κ x₀) :
    A.box ⊆ {x | PositiveState x} := by
  intro x hx i
  exact A.parameter_pos.trans_le (hx.1 i)

/-- Transfer the inward estimate from exponential coordinates to every physical
point of the box. Strict positivity follows from box membership, not from an
unproved positivity theorem for trajectories. -/
theorem inward_on_box (A : AffineBarrierData N κ x₀)
    {x : Fin d → ℝ} (hx : x ∈ A.box) {j : Fin A.n}
    (hj : AffineActive A.slope A.offset x j) :
    0 ≤ dot (A.slope j) (massAction N κ x) := by
  obtain ⟨hpositive, hunit, hrec⟩ :=
    reciprocal_box_log_coordinates A.parameter_pos A.parameter_lt_one hx
  have heq : (fun i => A.parameter ^ (Real.log (x i) / Real.log A.parameter)) = x :=
    funext hrec
  have ha : AffineActive A.slope A.offset
      (fun i => A.parameter ^ (Real.log (x i) / Real.log A.parameter)) j := by
    simpa only [heq] using hj
  have hi := A.inward (fun i => Real.log (x i) / Real.log A.parameter) hunit j ha
  simpa only [heq] using hi

/-- A frontier point has an exponent coordinate of absolute value one, where
the constant branch cannot be active. -/
theorem constant_not_active_on_frontier (A : AffineBarrierData N κ x₀)
    {x : Fin d → ℝ} (hx : x ∈ frontier A.box) :
    ¬ AffineActive A.slope A.offset x A.constant_branch := by
  have hxbox := A.isClosed_box.frontier_subset hx
  obtain ⟨hpositive, hunit, hrec⟩ :=
    reciprocal_box_log_coordinates A.parameter_pos A.parameter_lt_one hxbox
  have heq : (fun i => A.parameter ^ (Real.log (x i) / Real.log A.parameter)) = x :=
    funext hrec
  have hboundary := reciprocal_box_frontier_coordinate
    A.parameter_pos A.parameter_lt_one hx
  have ha := A.boundary_excluded
    (fun i => Real.log (x i) / Real.log A.parameter) hunit hboundary
  simpa only [heq] using ha

theorem plateau_disjoint_frontier (A : AffineBarrierData N κ x₀) :
    Disjoint A.plateau (frontier A.box) := by
  apply Set.disjoint_left.mpr
  intro x hx hxb
  exact A.constant_not_active_on_frontier hxb ((A.mem_plateau_iff_active x).mp hx)

theorem plateau_isFinitePolyhedron (A : AffineBarrierData N κ x₀) :
    IsFinitePolyhedron A.plateau :=
  finiteAffine_superlevel_isFinitePolyhedron A.slope A.offset (A.offset A.constant_branch)

theorem plateau_subset_interior_box (A : AffineBarrierData N κ x₀) :
    A.plateau ⊆ interior A.box :=
  Geometry.subset_interior_of_disjoint_frontier A.plateau_isFinitePolyhedron.convex.isPreconnected
    ⟨x₀, A.initial_mem_plateau, A.initial_mem_interior_box⟩ A.plateau_disjoint_frontier

theorem isCompact_plateau (A : AffineBarrierData N κ x₀) : IsCompact A.plateau :=
  A.isCompact_box.of_isClosed_subset A.plateau_isFinitePolyhedron.isClosed
    (A.plateau_subset_interior_box.trans interior_subset)

theorem plateau_subset_positive (A : AffineBarrierData N κ x₀) :
    A.plateau ⊆ {x | PositiveState x} :=
  A.plateau_subset_interior_box.trans (interior_subset.trans A.box_subset_positive)

/-- The plateau is a compact convex polyhedron containing the initial point
and lying strictly in the positive orthant. -/
theorem geometric_properties (A : AffineBarrierData N κ x₀) :
    IsCompact A.plateau ∧ Convex ℝ A.plateau ∧ IsFinitePolyhedron A.plateau ∧
      x₀ ∈ A.plateau ∧ A.plateau ⊆ {x | PositiveState x} :=
  ⟨A.isCompact_plateau, A.plateau_isFinitePolyhedron.convex, A.plateau_isFinitePolyhedron,
    A.initial_mem_plateau, A.plateau_subset_positive⟩

end Problem326.BarrierConstruction.AffineBarrierData

end

end OAI
