import OAI.Analysis.CircleDomains.Transfer.GeometricCompletion

namespace OAI

/-!
# From physical grid avoidance to inactive staircase branches

At reciprocal spacing every integer lattice level represents one of the
finite circle levels. Consequently the actual physical boundary avoidance
constructed by the contour theorem gives exactly the shifted-lattice
avoidance needed by the smooth filling theorem, including for local real
lifts of circle coordinates.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_reciprocal_level_of_mem_lattice
    {N : ℕ} {θ r : ℝ} (hr : r ∈ shiftedLattice (reciprocalGridStep N) θ) :
    ∃ j : Fin (N + 1), (r : UnitAddCircle) =
      ((θ + (j.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle) := by
  obtain ⟨k, rfl⟩ := hr
  have hm0 : 0 ≤ k % (N + 1 : ℤ) := Int.emod_nonneg _ (by omega)
  have hmN : k % (N + 1 : ℤ) < N + 1 := Int.emod_lt_of_pos _ (by omega)
  let j : Fin (N + 1) := ⟨(k % (N + 1 : ℤ)).toNat, by omega⟩
  have hj : (j.val : ℤ) = k % (N + 1 : ℤ) := Int.toNat_of_nonneg hm0
  have hki : k = (j.val : ℤ) + (k / (N + 1 : ℤ)) * (N + 1 : ℤ) := by
    rw [hj]
    nlinarith [Int.emod_add_mul_ediv k (N + 1 : ℤ)]
  have hk : (k : ℝ) = (j.val : ℝ) + ((k / (N + 1 : ℤ) : ℤ) : ℝ) * ((N : ℝ) + 1) := by
    exact_mod_cast hki
  refine ⟨j, (addCircle_eq_iff_exists_int 1 _ _).mpr ⟨k / (N + 1 : ℤ), ?_⟩⟩
  calc
    θ + reciprocalGridStep N * (k : ℝ) = θ + (j.val : ℝ) * reciprocalGridStep N +
        ((k / (N + 1 : ℤ) : ℤ) : ℝ) * (reciprocalGridStep N * ((N : ℝ) + 1)) := by
      rw [hk]
      ring
    _ = _ := by rw [reciprocalGridStep_mul_denominator]

theorem mem_reciprocal_grid_of_lift_lattice
    {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    {f : X → ℝ} (hf : ContinuousOn f U) {x : X} (hx : x ∈ U)
    {N : ℕ} {θ r : ℝ} (hlift : (r : UnitAddCircle) = (f x : UnitAddCircle))
    (hr : r ∈ shiftedLattice (reciprocalGridStep N) θ) :
    x ∈ ⋃ j, reciprocalBandLevel U f θ N j := by
  obtain ⟨j, hj⟩ := exists_reciprocal_level_of_mem_lattice hr
  exact mem_iUnion.mpr ⟨j, (circleBandGraph_on_open hU hf hx).mpr (hlift.symm.trans hj)⟩

/-- A local branch projecting to the original circle coordinate inherits
exact shifted-lattice avoidance from the physical quotient grid. -/
theorem branch_image_disjoint_lattice_of_boundary_grid_avoidance
    {X Y : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    {f : X → ℝ} (hf : ContinuousOn f U) (q : Y → X) (A : Set Y)
    (u : Y → ℝ) (hA : ∀ y ∈ A, q y ∈ U)
    (hlift : ∀ y ∈ A, (u y : UnitAddCircle) = (f (q y) : UnitAddCircle))
    {N : ℕ} {θ : ℝ}
    (havoid : Disjoint A (q ⁻¹' (⋃ j, reciprocalBandLevel U f θ N j))) :
    Disjoint (u '' A) (shiftedLattice (reciprocalGridStep N) θ) := by
  apply Set.disjoint_left.mpr
  rintro r ⟨y, hy, rfl⟩ hr
  exact Set.disjoint_left.mp havoid hy
    (mem_reciprocal_grid_of_lift_lattice hU hf (hA y hy) (hlift y hy) hr)

/-- A possible exception indexed in the natural numbers can be replaced
by one actual coordinate, even if the exception lies outside the list. -/
theorem exists_active_coordinate_of_single_exception
    {n : ℕ} (hn : 0 < n) (P : Fin n → Prop)
    (hP : ∃ k : ℕ, ∀ i : Fin n, i.val ≠ k → P i) :
    ∃ a : Fin n, ∀ i, i ≠ a → P i := by
  obtain ⟨k, hk⟩ := hP
  by_cases hkn : k < n
  · refine ⟨⟨k, hkn⟩, fun i hi => hk i ?_⟩
    exact fun heq => hi (Fin.ext heq)
  · exact ⟨⟨0, hn⟩, fun i _ => hk i (by omega)⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
