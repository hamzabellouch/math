import OAI.Geometry.SurfaceImmersion.Correction.UniformInputAtlasMeanData
import OAI.Geometry.Immersion.ClosedSurface.PhaseWeights

namespace OAI

/-! Actual atlas phase cutoffs discharge the geometric identities required
by finite mean adjustment. -/
noncomputable section
open Set Manifold TopologicalSpace
open scoped ContDiff Manifold Topology NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- The supported cutoff, phase, and coefficient form are constructed from
the fixed atlas weights and phase bases. No solver or cutoff is supplied for
the varying map. -/
theorem uniform_atlas_phase_mean_data_all_profiles
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (Ω U K : A.centers → Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ i j, IsOpen (Ω i j)) (hU : ∀ i j, IsOpen (U i j))
    (hK : ∀ i j, IsCompact (K i j))
    (hUK : ∀ i j, U i j ⊆ K i j) (hKΩ : ∀ i j, K i j ⊆ Ω i j)
    (hImm : ∀ i j x, x ∈ Ω i j → Function.Injective
      (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ i j x, x ∈ Ω i j →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j))
    (hsupport : ∀ i j, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ U i j)
    (U₀ : A.centers → Set JetPolynomial.Base) (hU₀ : ∀ i, IsOpen (U₀ i))
    (K₀ : A.centers → Compacts JetPolynomial.Base)
    (hU₀K : ∀ i, U₀ i ⊆ K₀ i)
    (hSU₀ : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U₀ i)
    {r ρ R : ℝ} (reference : A.centers → SmallModes.Base → Tensor)
    (hmargin : ∀ i j x, x ∈ U i j →
      ρ + ‖(Q i).Q j‖*r ≤ (Q i).Q j (reference i x) ∧
      (Q i).Q j (reference i x) ≤ R - ‖(Q i).Q j‖*r)
    : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (P : ℕ → ℝ), (∀ m, 0 ≤ P m) →
    ∃ p : A.centers → Fin 3 → ChartedMeanProfile emptyMetricPolynomial,
      ∀ (G : M → Space) (_hG : ContMDiff planeModel spaceModel ∞ G) (B : ℝ),
        0 ≤ B → B < ρ₀ → A.WeightedBound 1 2 B (G-F) →
        ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
        ∀ (τ r' : ℝ), r' ≤ r →
        ∃ d : ∀ i, ChartedMeanFamilyData emptyMetricPolynomial 0 τ s r' ρ R (reference i),
          (∀ i, (d i).Fits (p i)) ∧
          (∀ i, (d i).G = A.jetChartMap i G) ∧
          (∀ i, (d i).phase = fun j =>
            phaseLinear (w i j • (Q i).ξ j) ∘ planeCoordinateIsometry) ∧
          (∀ i, (d i).support = fun _ => A.chartWeightCompact i) ∧
          (∀ i j, coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j)) ∧
          (∀ i j x, x ∈ ((d i).solver j).e.source →
            ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j) ∧
          (∀ i j x, x ∈ ((d i).solver j).e.source →
            ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j) ∧
          (∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source) := by
  classical
  let ξ := fun i j => w i j • (Q i).ξ j
  have hξ (i j) : ξ i j ≠ 0 := smul_ne_zero (hw i j) ((Q i).nonzero j)
  let e := fun i j => linearPhaseChart (ξ i j) (hξ i j) (U i j) (hU i j)
  let φ : A.centers → Fin 3 → JetPolynomial.Base → ℝ :=
    fun i j => phaseLinear (ξ i j) ∘ planeCoordinateIsometry
  have hφ (i j) : ContDiff ℝ ∞ (φ i j) :=
    (phaseLinear (ξ i j)).contDiff.comp planeCoordinateIsometry.contDiff
  have hphase (i j) : coordinatePhase (φ i j) = phaseLinear (ξ i j) := by
    funext x
    change phaseLinear (ξ i j) (planeCoordinateIsometry (planeCoordinateIsometry.symm x)) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  let ψ := fun i j => A.phaseWeightCutoff i (e i j)
    (linearPhaseChart_smooth (ξ i j) (hξ i j) (U i j) (hU i j)).2.contDiffOn
    (hsupport i j) (w i j)
  obtain ⟨ρ₀,hρ₀,hall⟩ := A.uniform_input_atlas_mean_data_all_profiles F hF Ω U K hΩ hU hK hUK hKΩ
    ξ hξ hImm (fun i j x hx => good_smul (hw i j) (hgood i j x hx))
    (fun i _ => A.chartWeightCompact i) hsupport U₀ hU₀ K₀ hU₀K (fun i _ => hSU₀ i)
    φ hφ hphase ψ (fun i j => (Q i).Q j) reference hmargin
  refine ⟨ρ₀,hρ₀,?_⟩
  intro P hP
  obtain ⟨p,hdata⟩ := hall P hP
  refine ⟨p,?_⟩
  intro G hG B hB hBρ hclose s hs hs1 hp τ r' hr
  obtain ⟨d,hfit,hmap,hphases,hsupp,he,hcut,hform⟩ :=
    hdata G hG B hB hBρ hclose s hs hs1 hp τ r' hr
  refine ⟨d,hfit,hmap,hphases,hsupp,?_,?_,?_,?_⟩
  · intro i j
    rw [hphases i]
    exact hphase i j
  · intro i j x hx
    have hx' : x ∈ (e i j).source := by simpa only [he i j] using hx
    calc
      ((d i).data j).cutoff (((d i).solver j).e x) = ψ i j (((d i).solver j).e x) :=
        hcut i j _
      _ = ψ i j (e i j x) := congrArg (ψ i j)
        (congrArg (fun e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base => e x) (he i j))
      _ = A.planeWeight i x / w i j := A.phaseWeightCutoff_apply i (e i j)
        (linearPhaseChart_smooth (ξ i j) (hξ i j) (U i j) (hU i j)).2.contDiffOn
        (hsupport i j) (w i j) hx'
  · intro i j x _
    rw [hform i j]
  · intro i j x hx
    have hx' : x ∈ (e i j).source :=
      A.planeWeight_support_chart i (e i j) (hsupport i j) hx
    simpa only [he i j] using hx'

/-- The supported cutoff, phase, and coefficient form are constructed from
the fixed atlas weights and phase bases. No solver or cutoff is supplied for
the varying map. -/
theorem uniform_atlas_phase_mean_data
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (Ω U K : A.centers → Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ i j, IsOpen (Ω i j)) (hU : ∀ i j, IsOpen (U i j))
    (hK : ∀ i j, IsCompact (K i j))
    (hUK : ∀ i j, U i j ⊆ K i j) (hKΩ : ∀ i j, K i j ⊆ Ω i j)
    (hImm : ∀ i j x, x ∈ Ω i j → Function.Injective
      (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ i j x, x ∈ Ω i j →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j))
    (hsupport : ∀ i j, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ U i j)
    (U₀ : A.centers → Set JetPolynomial.Base) (hU₀ : ∀ i, IsOpen (U₀ i))
    (K₀ : A.centers → Compacts JetPolynomial.Base)
    (hU₀K : ∀ i, U₀ i ⊆ K₀ i)
    (hSU₀ : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U₀ i)
    {r ρ R : ℝ} (reference : A.centers → SmallModes.Base → Tensor)
    (hmargin : ∀ i j x, x ∈ U i j →
      ρ + ‖(Q i).Q j‖*r ≤ (Q i).Q j (reference i x) ∧
      (Q i).Q j (reference i x) ≤ R - ‖(Q i).Q j‖*r)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) :
    ∃ (ρ₀ : ℝ) (p : A.centers → Fin 3 → ChartedMeanProfile emptyMetricPolynomial),
      0 < ρ₀ ∧ ∀ (G : M → Space) (_hG : ContMDiff planeModel spaceModel ∞ G) (B : ℝ),
        0 ≤ B → B < ρ₀ → A.WeightedBound 1 2 B (G-F) →
        ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
        ∀ (τ r' : ℝ), r' ≤ r →
        ∃ d : ∀ i, ChartedMeanFamilyData emptyMetricPolynomial 0 τ s r' ρ R (reference i),
          (∀ i, (d i).Fits (p i)) ∧
          (∀ i, (d i).G = A.jetChartMap i G) ∧
          (∀ i, (d i).phase = fun j =>
            phaseLinear (w i j • (Q i).ξ j) ∘ planeCoordinateIsometry) ∧
          (∀ i, (d i).support = fun _ => A.chartWeightCompact i) ∧
          (∀ i j, coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j)) ∧
          (∀ i j x, x ∈ ((d i).solver j).e.source →
            ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j) ∧
          (∀ i j x, x ∈ ((d i).solver j).e.source →
            ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j) ∧
          (∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source) := by
  obtain ⟨ρ₀,hρ₀,hall⟩ := A.uniform_atlas_phase_mean_data_all_profiles F hF Q w hw Ω U K
    hΩ hU hK hUK hKΩ hImm hgood hsupport U₀ hU₀ K₀ hU₀K hSU₀ reference hmargin
  obtain ⟨p,hdata⟩ := hall P hP
  exact ⟨ρ₀,p,hρ₀,hdata⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
