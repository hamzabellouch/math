import OAI.Analysis.CircleDomains.Topology.BoundaryGridAvoidance

namespace OAI

/-!
# Smooth coordinate fillings from the actual boundary grids

The contour theorem gives one possible active label at each boundary.
The reciprocal-grid calculation turns its avoidance conclusions into
inactive-lattice avoidance for the actual local real branches. Thus the
smooth filling theorem applies at all sufficiently small widths.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem frontier_realJordanInterior (H : ℂ ≃ₜ ℂ) :
    frontier (realJordanInterior H) =
      Complex.equivRealProdCLM '' frontier (jordanInterior H) := by
  exact (Complex.equivRealProdCLM.toHomeomorph.image_frontier _).symm

theorem branch_avoids_lattice_on_real_boundary
    {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    {f : X → ℝ} (hf : ContinuousOn f U) (q : ℂ → X) (H : ℂ ≃ₜ ℂ)
    (u : (ℝ × ℝ) → ℝ)
    (hUq : ∀ z ∈ frontier (jordanInterior H), q z ∈ U)
    (hlift : ∀ z ∈ frontier (jordanInterior H),
      (u (Complex.equivRealProdCLM z) : UnitAddCircle) = (f (q z) : UnitAddCircle))
    {N : ℕ} {θ : ℝ}
    (havoid : Disjoint (frontier (jordanInterior H))
      (q ⁻¹' (⋃ j, reciprocalBandLevel U f θ N j))) :
    Disjoint (u '' frontier (realJordanInterior H)) (shiftedLattice (reciprocalGridStep N) θ) := by
  apply Set.disjoint_left.mpr
  rintro r ⟨x, hx, rfl⟩ hr
  rw [frontier_realJordanInterior] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  exact Set.disjoint_left.mp havoid hz
    (mem_reciprocal_grid_of_lift_lattice hU hf (hUq z hz) (hlift z hz) hr)

/-- The active label and all inactive lattice-avoidance premises are
constructed from the physical contour output. Only the actual local
branches and collar agreement remain as coordinate data. -/
theorem eventually_filled_coordinates_from_boundary_grids
    {I : Type*} [Fintype I] {n N : ℕ} (hn : 0 < n)
    (H : I → ℂ ≃ₜ ℂ)
    (hH : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (f : Fin n → X → ℝ) (hf : ∀ l, ContinuousOn (f l) U) (q : ℂ → X)
    (hUq : ∀ i z, z ∈ frontier (jordanInterior (H i)) → q z ∈ U)
    (θ : Fin n → ℝ)
    (hgrid : ∀ i, ∃ k : ℕ, ∀ l : Fin n, l.val ≠ k →
      Disjoint (frontier (jordanInterior (H i)))
        (q ⁻¹' (⋃ j, reciprocalBandLevel U (f l) (θ l) N j)))
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hHO : ∀ i, frontier (realJordanInterior (H i)) ⊆ O i)
    (u : I → Fin n → (ℝ × ℝ) → ℝ) (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (hlift : ∀ i l z, z ∈ frontier (jordanInterior (H i)) →
      (u i l (Complex.equivRealProdCLM z) : UnitAddCircle) = (f l (q z) : UnitAddCircle))
    (v : ℝ → Fin n → (ℝ × ℝ) → ℝ) (Ω : Set (ℝ × ℝ))
    (hv : ∀ δ, 0 < δ → δ < reciprocalGridStep N / 4 → ∀ l x, x ∈ Ω →
      (∀ i, x ∉ realJordanInterior (H i)) → ContDiffAt ℝ ∞ (v δ l) x)
    (hbranch : ∀ δ i l, EqOn (v δ l)
      (fun x => shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l x)) (O i)) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : Fin n → (ℝ × ℝ) → ℝ,
      IsFilledCoordinateFamily (fun i => realJordanInterior (H i)) Ω (v δ) F := by
  have hactive (i : I) : ∃ a : Fin n, ∀ l, l ≠ a →
      Disjoint (u i l '' frontier (realJordanInterior (H i)))
        (shiftedLattice (reciprocalGridStep N) (θ l)) := by
    apply exists_active_coordinate_of_single_exception hn
    obtain ⟨k, hk⟩ := hgrid i
    refine ⟨k, fun l hl => ?_⟩
    exact branch_avoids_lattice_on_real_boundary hU (hf l) q (H i) (u i l)
      (hUq i) (hlift i l) (hk l hl)
  choose active hactive using hactive
  exact eventually_exists_filled_jordan_coordinates H hH O hO hHO u hu active
    (reciprocalGridStep_pos N) θ hactive v Ω hv hbranch

/-- For real coordinates, the collars and their branch agreement are
constructed directly from the region where the actual cutoff equals one. -/
theorem eventually_fill_actual_cutoff_coordinates
    {I : Type*} [Fintype I] {n N : ℕ} (hn : 0 < n)
    (H : I → ℂ ≃ₜ ℂ)
    (hH : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {G : Set (ℝ × ℝ)} (hG : IsOpen G)
    (u : Fin n → (ℝ × ℝ) → ℝ) (hu : ∀ l, ContDiffOn ℝ ∞ (u l) G)
    (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hboundary : ∀ i z, z ∈ frontier (jordanInterior (H i)) →
      Complex.equivRealProdCLM z ∈ G ∩ interior {x | χ x = 1})
    {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (f : Fin n → X → ℝ) (hf : ∀ l, ContinuousOn (f l) U) (q : ℂ → X)
    (hUq : ∀ i z, z ∈ frontier (jordanInterior (H i)) → q z ∈ U)
    (hlift : ∀ i l z, z ∈ frontier (jordanInterior (H i)) →
      (u l (Complex.equivRealProdCLM z) : UnitAddCircle) = (f l (q z) : UnitAddCircle))
    (θ : Fin n → ℝ)
    (hgrid : ∀ i, ∃ k : ℕ, ∀ l : Fin n, l.val ≠ k →
      Disjoint (frontier (jordanInterior (H i)))
        (q ⁻¹' (⋃ j, reciprocalBandLevel U (f l) (θ l) N j))) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : Fin n → (ℝ × ℝ) → ℝ,
      IsFilledCoordinateFamily (fun i => realJordanInterior (H i))
        (G ∪ ⋃ i, realJordanInterior (H i))
        (cutoffCoordinateFamily u χ (reciprocalGridStep N) δ θ) F := by
  let O : Set (ℝ × ℝ) := G ∩ interior {x | χ x = 1}
  have hO : IsOpen O := hG.inter isOpen_interior
  have hHO (i : I) : frontier (realJordanInterior (H i)) ⊆ O := by
    rw [frontier_realJordanInterior]
    rintro x ⟨z, hz, rfl⟩
    exact hboundary i z hz
  apply eventually_filled_coordinates_from_boundary_grids hn H hH U hU f hf q hUq θ hgrid
    (fun _ => O) (fun _ => hO) hHO (fun _ => u)
    (fun _ l => (hu l).mono inter_subset_left) hlift
    (fun δ => cutoffCoordinateFamily u χ (reciprocalGridStep N) δ θ)
    (G ∪ ⋃ i, realJordanInterior (H i))
  · intro δ hδ hδh l x hx hnot
    have hxG : x ∈ G := by
      rcases hx with hx | hx
      · exact hx
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact (hnot i hi).elim
    exact (contDiffOn_cutoff_shiftedStaircase (hu l) hχ.contDiffOn
      (reciprocalGridStep_pos N) hδ hδh (θ l)).contDiffAt (hG.mem_nhds hxG)
  · intro δ i l x hx
    exact cutoffStaircase_of_one
      ((interior_subset : interior {y | χ y = 1} ⊆ {y | χ y = 1}) hx.2)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
