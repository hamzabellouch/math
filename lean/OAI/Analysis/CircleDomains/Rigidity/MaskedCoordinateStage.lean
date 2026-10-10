import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Rigidity.MaskedCoordinateModel

namespace OAI

/-! One finite transfer of the given coordinate family, retaining the
actual model and every nonsingular terminal branch estimate. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure MaskedCoordinateStage {S : Type*} {n : ℕ} {G U : Set Sphere}
    {π : Sphere → Sphere} {σ : S → Sphere} (C : Fin n → MaskedCoordinateData G U π σ)
    (Flag : Set S) (O : S → Set Sphere) (K₀ : Set (ℝ × ℝ)) (ε ρ : ℝ) (k₀ : ℕ) where
  indices : Set S
  indices_finite : indices.Finite
  flags : Flag ⊆ indices
  terminals : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : indices => σ s) (fun s => O s)
  fillCount : ℕ
  filling : Fin fillCount → ℂ ≃ₜ ℂ
  core : Set (ℝ × ℝ)
  core_closed : IsClosed core
  core_contains : K₀ ⊆ interior core
  core_source : core ⊆ realChartDomain G
  core_cocompact : IsCompact (closure coreᶜ)
  core_model : sphericalCore core ⊆ openCompletedRegion terminals.H
  cutoff : (ℝ × ℝ) → ℝ
  grid : ℕ
  offset : Fin n → ℝ
  small_grid : reciprocalGridStep grid < ρ
  model : MaskedModelData terminals.H filling (realChartDomain G) core
    (fun l => physicalMask π (C l).mask) (fun l => (C l).physical) cutoff grid offset ε
  late_width : k₀ ≤ model.widthIndex
  terminal_domain : indices → Set (ℝ × ℝ)
  terminal_branch : indices → Fin n → (ℝ × ℝ) → ℝ
  terminal_open : ∀ s, IsOpen (terminal_domain s)
  terminal_frontier : ∀ s, frontier (realJordanInterior (terminals.H s)) ⊆ terminal_domain s
  terminal_lift : ∀ l (s : indices), σ s ∈ (C l).mask → σ s ≠ σ (C l).singular →
    ContDiffOn ℝ ∞ (terminal_branch s l) (terminal_domain s) ∧
    ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior (terminals.H s))),
      (terminal_branch s l x : UnitAddCircle) = model.functions l x
  terminal_excess : ∀ l, Real.sqrt
    (∑' s : {s : indices // σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular},
      max (Metric.diam (terminal_branch s l '' frontier (realJordanInterior (terminals.H s))) -
        ((C l).upper s - (C l).lower s)) 0 ^ 2) < ε

theorem nonempty_masked_coordinate_stage
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    {G U : Set Sphere} (hG : IsOpen G) (hinfty : OnePoint.infty ∈ G)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ)) (hUB : U ⊆ (π '' Gᶜ)ᶜ)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    {K₀ : Set (ℝ × ℝ)} (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ realChartDomain G)
    {n : ℕ} (hn : 0 < n) {S : Type*} [Countable S]
    (σ : S → Sphere) (hσ : Injective σ) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (hσU : ∀ s, σ s ∉ U) (C : Fin n → MaskedCoordinateData G U π σ)
    (Flag : Set S) (hFlag : Flag.Finite) (hflag : ∀ l, (C l).singular ∈ Flag)
    (hcompat : ∀ (j : Fin n) (d : ℕ) (labels : Fin d → Fin n),
      (∀ i, (labels i).val < j.val) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (C j).graph (fun l => (C l).graph) labels) = 0)
    (O : S → Set Sphere) (hO : ∀ s, O s ∈ 𝓝 (σ s))
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (k₀ : ℕ) :
    Nonempty (MaskedCoordinateStage C Flag O K₀ ε ρ k₀) := by
  obtain ⟨K, χ, N, θ, hA, D, m, H, Q, hk, hK, hK₀K, hKG, hKc, hKQ, hN,
      E, w, hE, hw, hexcess⟩ :=
    exists_model_of_masked_coordinates hsard hsch hcompact hfinite hG hinfty
      π hπ hclosed hsurj hr hTD hUB hPU hK₀ hK₀G hn σ hσ hσB hσU C Flag hFlag hflag
      hcompat O hO hε hρ k₀
  exact ⟨{
    indices := gridTerminalIndices Flag (reciprocalGridStep N) upperPair
      (fun l => (C l).lower) (fun l => (C l).upper) θ
    indices_finite := hA
    flags := fun _ hs => Or.inl hs
    terminals := D
    fillCount := m
    filling := H
    core := K
    core_closed := hK
    core_contains := hK₀K
    core_source := hKG
    core_cocompact := hKc
    core_model := hKQ
    cutoff := χ
    grid := N
    offset := θ
    small_grid := hN
    model := Q
    late_width := hk
    terminal_domain := E
    terminal_branch := w
    terminal_open := fun s => (hE s).1
    terminal_frontier := fun s => (hE s).2
    terminal_lift := hw
    terminal_excess := hexcess }⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
