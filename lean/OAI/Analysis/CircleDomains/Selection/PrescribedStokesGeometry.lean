import OAI.Analysis.CircleDomains.Rigidity.MaskedStokesGeometry

namespace OAI

/-! The retained-collar geometry uses any prescribed actual round coordinates
of the terminal assignment, including the coordinates of a normal limit. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateStage.exists_stokes_collar_geometry_prescribed
    (hsch : PlanarSchoenflies)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n)
    (hinf : OnePoint.infty ∈ G) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (H : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ openCompletedRegion T.terminals.H)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (C l).mask))
    (s : T.indices)
    (hs : closedTerminalCap (T.terminals.H s) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H)
    (a : TerminalComponentAssignment T.terminals.H T.model.forward T.model.domain) :
    ∀ (c : T.indices → ℂ) (r : T.indices → ℝ), (∀ i, 0 ≤ r i) →
    (∀ i, connectedComponentIn T.model.domainᶜ (a.point i) =
      ((↑) : ℂ → Sphere) '' closedBall (c i) (r i)) →
    Pairwise (Disjoint on fun i => closedBall (c i) (r i)) →
    ((↑) : ℂ → Sphere) ⁻¹' T.model.domain = (⋃ i, closedBall (c i) (r i))ᶜ →
    ∃ D : StokesCollarGeometry T l s H a, D.center = c ∧ D.radius = r := by
  intro c r hr he hd hext
  classical
  let : Fintype T.indices := T.indices_finite.fintype
  have hi : OnePoint.infty ∈ openCompletedRegion T.terminals.H :=
    T.core_model (infty_mem_sphericalCore T.core)
  obtain ⟨J, m, κ, hκ, hJ, hinside, hexact, hregion⟩ :=
    T.exists_collar_region hsch l H hbd hmask c r hext
  have hside := open_image_retained_jordan_side_eq
    (isOpen_openCompletedRegion T.terminals.H)
    (isConnected_openCompletedRegion T.terminals.H T.terminals.disjoint_closures).isPreconnected
    hi H J hbd (fun p hp => (T.model.equivalence.smooth p hp).1.continuousWithinAt)
    (fun _ hW hWQ => T.model.equivalence.isOpen_image T.model.circle_domain.1 hW hWQ)
    T.model.equivalence.bijOn.injOn T.model.principal.1 hJ
  rw [T.model.equivalence.bijOn.image_eq] at hside
  have hbdJ : ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) ⊆ T.model.domain := by
    rw [← hJ]
    exact (image_mono hbd).trans (image_subset_iff.mpr T.model.equivalence.mapsTo)
  have hsJ := a.target_inside_of_source_inside T.terminals.disjoint_closures
    T.model.equivalence H J hbdJ hside s hs
  have hsball : closedBall (c s) (r s) ⊆ jordanInterior J := by
    intro z hz
    have h := hsJ (he s ▸ mem_image_of_mem ((↑) : ℂ → Sphere) hz)
    exact OnePoint.coe_injective.mem_set_image.mp h
  obtain ⟨b, hb⟩ := (hexact s).mpr hsball
  refine ⟨{
    center := c
    radius := r
    radius_nonneg := hr
    disks := he
    disjoint := hd
    exterior := hext
    target := J
    boundary := hJ
    count := m
    label := κ
    injective := hκ
    base := b
    distinguished := hb
    inside := hinside
    mask := ?_
    region := hregion }, rfl, rfl⟩
  intro j
  apply T.label_mem_mask_of_terminal_inside l hinf hσB H hmask (κ j)
  exact a.source_inside_of_target_inside T.model.equivalence c r hr hd hext
    (fun i => he i ▸ Subset.rfl) H J hbd hside (κ j) (hinside j)


end CircleDomainRigidity.FiniteTransfer

end

end OAI
