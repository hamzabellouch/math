import OAI.Analysis.CircleDomains.Transfer.CompletedChart
import OAI.Analysis.CircleDomains.Transfer.GridCoordinateFilling
import OAI.Analysis.CircleDomains.Transfer.CofiniteTransfer

namespace OAI

/-!
# Real-coordinate transfer on the actual finite completion

The geometric completion, actual reciprocal-grid collars and selected
wedge cost produce transferred coordinates on the whole completed region
and a spherical-background metric with total and localized energy bounds.
This assembles the real-coordinate part of finite transfer; periodic
coordinates and the terminal oscillation bookkeeping remain separate.
-/

open Set Filter MeasureTheory Finset Function
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem real_coordinate_transfer_from_grid
    {I J : Type*} [Fintype J] {n N : ℕ} (hn : 0 < n)
    (T : I → ℂ ≃ₜ ℂ) (H : J → ℂ ≃ₜ ℂ)
    (hH : Pairwise (Disjoint on fun j => closure (jordanInterior (H j))))
    {G B : Set Sphere} (hG : IsOpen G) (π : Sphere → Sphere)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (hcover : π ⁻¹' B ⊆ sphericalDiskUnion T ∪ sphericalDiskUnion H)
    {K : Set (ℝ × ℝ)} (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (hKG : K ⊆ realChartDomain G)
    (u : Fin n → (ℝ × ℝ) → ℝ) (hu : ∀ l, ContDiffOn ℝ ∞ (u l) (realChartDomain G))
    (hu2 : ∀ l, MemLp (planarGradient (u l)) 2 (volume.restrict (realChartDomain G)))
    (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχzero : ∀ᶠ z in 𝓝ˢ K, χ z = 0)
    (hHC : ∀ j, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (H j))) (cutoffCore χ))
    (hboundary : ∀ j z, z ∈ frontier (jordanInterior (H j)) → (z : Sphere) ∈ G)
    {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (f : Fin n → X → ℝ) (hf : ∀ l, ContinuousOn (f l) U) (q : ℂ → X)
    (hUq : ∀ j z, z ∈ frontier (jordanInterior (H j)) → q z ∈ U)
    (hlift : ∀ j l z, z ∈ frontier (jordanInterior (H j)) →
      (u l (Complex.equivRealProdCLM z) : UnitAddCircle) = (f l (q z) : UnitAddCircle))
    (θ : Fin n → ℝ)
    (hgrid : ∀ j, ∃ k : ℕ, ∀ l : Fin n, l.val ≠ k →
      Disjoint (frontier (jordanInterior (H j)))
        (q ⁻¹' (⋃ r, reciprocalBandLevel U (f l) (θ l) N r)))
    (hvi : ∀ k, IntegrableOn (coordinateWedges (natCoordinateFamily
      (cutoffCoordinateFamily u χ (reciprocalGridStep N)
        (staircaseWidth (reciprocalGridStep N) k) θ)) n) (realChartDomain G \ K))
    {ε : ℝ} (hgood : ∃ᶠ k in atTop,
      (∫ z in realChartDomain G \ K, coordinateWedges (natCoordinateFamily
        (cutoffCoordinateFamily u χ (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) k) θ)) n z) < ε / 2)
    (k₀ : ℕ) :
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → ℝ) (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric),
      k₀ ≤ k ∧ IsFilledCoordinateFamily (fun j => realJordanInterior (H j))
        (realChartDomain G ∪ ⋃ j, realJordanInterior (H j))
        (cutoffCoordinateFamily u χ (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) k) θ) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ l, F l z = u l z) ∧
      0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ l ∈ range n, ∫ z in realChartDomain (completedRegion T) \ K,
        gradientEnergy (natCoordinateFamily F l) g z) < ε ∧
      ∀ l : ℕ, l < n → ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in realChartDomain (completedRegion T) \ E,
          gradientEnergy (natCoordinateFamily F l) g z) <
          (∫ z in realChartDomain G \ E, gradientEnergy (natCoordinateFamily u l)
            (fun z => sphericalMetricFactor z • 1) z) + ε := by
  have hGp := isOpen_realChartDomain hG
  have hΩ : IsOpen (realChartDomain G ∪ ⋃ j, realJordanInterior (H j)) :=
    hGp.union (isOpen_iUnion fun j => (realJordanInterior_geometry (H j)).1)
  have hQΩ := real_completedRegion_subset_extension T H G B π hbad hcover
  have hKD := real_core_avoids_filling H (sphericalCore_subset_cutoffCore χ hχzero) hHC
  have hfill := eventually_fill_actual_cutoff_coordinates hn H hH hGp u hu χ hχ
    (real_boundary_in_domain_and_plateau H χ hboundary hHC) U hU f hf q hUq hlift θ hgrid
  have hretain (δ : ℝ) : ∀ᶠ z in 𝓝ˢ K, ∀ l,
      cutoffCoordinateFamily u χ (reciprocalGridStep N) δ θ l z = u l z :=
    cutoffStaircase_eventuallyEq_original u
      (fun l => shiftedStaircase (reciprocalGridStep N) δ (θ l)) χ hχzero
  have hgood2 : ∃ᶠ k in atTop,
      (∫ z in realChartDomain G \ K, 2 * coordinateWedges (natCoordinateFamily
        (cutoffCoordinateFamily u χ (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) k) θ)) n z) < ε := by
    apply hgood.mono
    intro k hk
    rw [integral_const_mul]
    linarith
  exact exists_cofinite_transfer_at_good_width (fun j => realJordanInterior (H j))
    (fun j => (realJordanInterior_geometry (H j)).1) hΩ (isClosed_real_completedRegion T) hQΩ
    hGp.measurableSet hK hKc hKG hQΩ hKD
    (fun δ => cutoffCoordinateFamily u χ (reciprocalGridStep N) δ θ) u hu2 hretain
    (reciprocalGridStep_pos N) hfill (fun k => (hvi k).const_mul 2) hgood2 k₀

end CircleDomainRigidity.FiniteTransfer

end

end OAI
