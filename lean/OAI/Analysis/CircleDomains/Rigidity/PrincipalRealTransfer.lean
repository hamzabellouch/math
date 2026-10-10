import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Transfer.RealGridTransfer
import OAI.Analysis.CircleDomains.Uniformization.RealFiniteModel

namespace OAI

/-!
# Normalized real-coordinate transfer from the geometric grid

The width, filled real functions and metric used for the energy estimates
also give the principal circle model and its genuine transported real
functions. The circle model uses only the cited compact metric and finite
connectivity uniformization inputs.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem principal_real_coordinate_transfer_from_grid
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {I J : Type*} [Finite I] [Fintype J] {n N : ℕ} (hn : 0 < n)
    (T : I → ℂ ≃ₜ ℂ) (H : J → ℂ ≃ₜ ℂ)
    (hT : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    (hH : Pairwise (Disjoint on fun j => closure (jordanInterior (H j))))
    {G B : Set Sphere} (hG : IsOpen G) (π : Sphere → Sphere)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (hcover : π ⁻¹' B ⊆ sphericalDiskUnion T ∪ sphericalDiskUnion H)
    {K : Set (ℝ × ℝ)} (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (hKG : K ⊆ realChartDomain G) (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (u : Fin n → (ℝ × ℝ) → ℝ) (hu : ∀ l, ContDiffOn ℝ ∞ (u l) (realChartDomain G))
    (hu2 : ∀ l, MemLp (planarGradient (u l)) 2 (volume.restrict (realChartDomain G)))
    (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχzero : ∀ᶠ z in 𝓝ˢ K, χ z = 0)
    (hHC : ∀ j, Disjoint (closedTerminalCap (H j)) (cutoffCore χ))
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
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → ℝ) (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric)
      (V : Set Sphere) (φ φi : Sphere → Sphere),
      k₀ ≤ k ∧ IsFilledCoordinateFamily (fun j => realJordanInterior (H j))
        (realChartDomain G ∪ ⋃ j, realJordanInterior (H j))
        (cutoffCoordinateFamily u χ (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) k) θ) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ l, F l z = u l z) ∧
      0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ l ∈ Finset.range n, ∫ z in realChartDomain (completedRegion T) \ K,
        gradientEnergy (natCoordinateFamily F l) g z) < ε ∧
      (∀ l : ℕ, l < n → ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in realChartDomain (completedRegion T) \ E,
          gradientEnergy (natCoordinateFamily F l) g z) <
          (∫ z in realChartDomain G \ E, gradientEnergy (natCoordinateFamily u l)
            (fun z => sphericalMetricFactor z • 1) z) + ε) ∧
      IsCircleDomain V ∧ IsSmoothSphereEquivalence φ φi (openCompletedRegion T) V ∧
      IsConformalOn φ (sphericalCore K) ∧ IsPrincipalNormalized φ ∧
      (∀ l, ContDiffOn ℝ ∞ (F l ∘ sphereRealMap φi) (realChartDomain V) ∧
        ∀ x ∈ realChartDomain (openCompletedRegion T),
          ((F l ∘ sphereRealMap φi) ∘ sphereRealMap φ) =ᶠ[𝓝 x] F l) ∧
      (∀ l (s : Set (ℝ × ℝ)), MeasurableSet s → s ⊆ realChartDomain (openCompletedRegion T) →
        (∫ y in sphereRealMap φ '' s,
          gradientEnergy (F l ∘ sphereRealMap φi) (fun _ => 1) y) =
          ∫ x in s, gradientEnergy (F l) g x) ∧
      (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g φ p) ∧
      (∀ l, IntegrableOn (gradientEnergy (F l) g) (realChartDomain (completedRegion T))) := by
  obtain ⟨k, F, R, g, hk, hF, hretain, hR, hg, hPD, hcore, hfar, htotal, hlocal⟩ :=
    real_coordinate_transfer_from_grid hn T H hH hG π hbad hcover hK hKc hKG
      u hu hu2 χ hχ hχzero hHC hboundary U hU f hf q hUq hlift θ hgrid hvi hgood k₀
  have hQΩ := real_completedRegion_subset_extension T H G B π hbad hcover
  obtain ⟨V, φ, φi, hV, heq, hconf, hnorm, hsmooth, henergy, hmetric⟩ :=
    finite_metric_model_with_real_fillings hcompact hfinite T hT hKQ hQΩ
      g hg hPD ⟨R, hR, hfar⟩ hcore hF
  refine ⟨k, F, R, g, V, φ, φi, hk, hF, hretain, hR, hg, hPD, hcore, hfar,
    htotal, hlocal, hV, heq, hconf, hnorm, hsmooth, henergy, hmetric, ?_⟩
  intro l
  apply integrableOn_gradientEnergy_with_cofinite_core
    ((isOpen_realChartDomain hG).union (isOpen_iUnion fun j =>
      (realJordanInterior_geometry (H j)).1))
    (isClosed_real_completedRegion T) hQΩ hK hKc hKG (hF.1 l)
    (integrable_gradientEnergy_spherical_of_memLp (hu2 l))
    (hretain.mono fun _ hz => hz l) hg.continuous hPD hcore

end CircleDomainRigidity.FiniteTransfer

end

end OAI
