import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSupportedMeanData
import OAI.Geometry.SurfaceImmersion.Atlas.GridCutoffBounds
import OAI.Geometry.SurfaceImmersion.Geometry.UniformCoefficientMargins
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasOuterDomains
import OAI.Geometry.SurfaceImmersion.Atlas.MetricAtlasReference
import OAI.Geometry.SurfaceImmersion.Correction.TensorAtlasMean
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasFiniteCancellation

namespace OAI

/-! Actual mean solvers for the variable grid, with common polynomial budgets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGrid PhaseGeometry RealModes
local instance gridMeanDataFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridMeanDataFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridMeanDataDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridMeanDataDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance gridMeanDataSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridMeanDataSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)


theorem polynomial_grid_mean_data (g : SmoothMetric M) {a₀ C₀ H : ℝ}
    (ha₀ : 0 < a₀) (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) :
    ∃ (p p' : ℕ → ℕ) (C C' L : ℕ → ℝ),
      (∀ m, 1 ≤ C m) ∧ (∀ m, 1 ≤ C' m) ∧ (∀ m, 1 ≤ L m) ∧
    ∃ r ρ R : ℝ, 0 < r ∧ 0 < ρ ∧ 0 < R ∧
    ∀ (z : ℝ) (hz : 0 < z), z ≤ 1 → ∀ a : A.centers → Finset Index,
      (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion (a i) (z^6)) →
    ∀ (Q : ∀ i, (a i) → PhaseBasis) (w : ∀ i, (a i) → Fin 3 → ℝ),
      (∀ i k j, 1 ≤ w i k j) → (∀ i k j, ‖(Q i k).Q j‖ ≤ C₀) →
      (∀ i k j x, (Q i k).Q j (A.tensorPlaneRead i g.inner x) ≤ H) →
      (∀ i k j x, x ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
        a₀ ≤ (Q i k).Q j (A.tensorPlaneRead i g.inner x)) →
    ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 → ∀ D : ℝ, 0 < D →
    ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) → (∀ m, 2*D ≤ B m ∧ C₀ ≤ B m) →
      (∀ i k j m, ‖w i k j • (Q i k).ξ j‖ ≤ B m ∧
        ∀ hξ : w i k j • (Q i k).ξ j ≠ 0,
          ‖(phaseEquiv (w i k j • (Q i k).ξ j) hξ).symm.toContinuousLinearMap‖ ≤ B m) →
      (∀ i m l, l ≤ m+3 → WeightedEstimates.WeightedBound univ 1 l
        (B m/(s : ℝ)^(l-2)) (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i k j x, x ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ∧
        Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
          (w i k j • (Q i k).ξ j) ∧
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x))⁻¹‖ ≤ D ∧
        ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
          (-(w i k j • (Q i k).ξ j).2,(w i k j • (Q i k).ξ j).1)‖⁻¹ ≤ D) →
      ∃ c : ∀ i (j : (a i) × Fin 3), PolynomialSolveData emptyMetricPolynomial 0
        (A.jetChartMap i F) (A.jetChartMap_smooth i hF)
        (phaseLinear (w i j.1 j.2 • (Q i j.1).ξ j.2) ∘ planeCoordinateIsometry)
        (A.cellChartCompact i (a i) (z^6) j.1.val) τ s,
      ∃ d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i g.inner),
        (∀ i j m, (c i j).C m = C m*(B m)^(p m) ∧
          (c i j).J m = 1+2*B m ∧ (c i j).D m = 0) ∧
        (∀ i j x, x ∈ (c i j).e.source → (d i j).cutoff ((c i j).e x) =
          supportedCellCutoff (A.supportedPlaneWeight i) (pow_pos hz 6)
            (hcover i) j.1.val x / w i j.1 j.2) ∧
        (∀ i j, (d i j).form = fun _ => (Q i j.1).Q j.2) ∧
        (∀ i j, tsupport (fun x => A.planeWeight i x * normalizedCutoff (a i) (z^6) j.1.val x) ⊆
          (c i j).e.source) ∧
        ∀ i j m, let b := linearMeanGeometryBudget p' C' B (fun l =>
          1+phaseCutoffBudget l (L l/z^(6*l)) (B l) 1) m;
          (d i j).budgets.inv m ≤ b ∧ (d i j).budgets.chi m ≤ b ∧
          (d i j).budgets.forms m ≤ b ∧ (d i j).budgets.pull m ≤ b ∧
          (d i j).budgets.psi m ≤ b ∧ (d i j).budgets.normal m ≤ b ∧ (d i j).budgets.mode m ≤ b := by
  classical
  obtain ⟨p,p',C,C',hC,hC',hmean⟩ := polynomial_supported_linear_mean_data
  obtain ⟨L,hL,hcut⟩ := A.grid_exact_cutoff_bounds
  obtain ⟨r,ρ,R,hr,hρ,hR,hmargin⟩ := uniform_coefficient_margins ha₀ hC₀ hH
  obtain ⟨U₀,K₀,hU₀,hUK,hKU,_⟩ := A.exists_outer_domains
  have hball := zero_lt_one.trans_le A.one_le_tensorReadBallConstant
  have hballr : A.tensorReadBallConstant*(r/A.tensorReadBallConstant) = r :=
    mul_div_cancel₀ r hball.ne'
  refine ⟨p,p',C,C',L,hC,hC',hL,r/A.tensorReadBallConstant,ρ,R,div_pos hr hball,hρ,hR,?_⟩
  intro z hz hz1 a hcover Q w hw hQ hup hlow F hF τ s hs hs1 D hD B hB hBD hphase hjets hgeom
  rw [hballr]
  let K := fun i (j : (a i) × Fin 3) => A.cellChartCompact i (a i) (z^6) j.1.val
  let φ := fun i (j : (a i) × Fin 3) =>
    phaseLinear (w i j.1 j.2 • (Q i j.1).ξ j.2) ∘ planeCoordinateIsometry
  have local_data (i : A.centers) (j : (a i) × Fin 3) :
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 (A.jetChartMap i F)
          (A.jetChartMap_smooth i hF) (φ i j) (K i j) τ s,
      ∃ d : ChartedMeanData c r ρ R (A.tensorPlaneRead i g.inner),
        (∀ m, c.C m = C m*(B m)^(p m)) ∧ (∀ m, c.J m = 1+2*B m) ∧
        (∀ m, c.D m = 0) ∧
        (∀ x ∈ c.e.source, d.cutoff (c.e x) =
          (w i j.1 j.2)⁻¹ * A.exactCellCutoff i (pow_pos hz 6) (hcover i) j.1.val x) ∧
        d.form = (fun _ => (Q i j.1).Q j.2) ∧
        ∀ m, let b := linearMeanGeometryBudget p' C' B (fun l =>
          1+phaseCutoffBudget l (L l/z^(6*l)) (B l) 1) m;
          d.budgets.inv m ≤ b ∧ d.budgets.chi m ≤ b ∧ d.budgets.forms m ≤ b ∧
          d.budgets.pull m ≤ b ∧ d.budgets.psi m ≤ b ∧ d.budgets.normal m ≤ b ∧ d.budgets.mode m ≤ b := by
    let ξ := w i j.1 j.2 • (Q i j.1).ξ j.2
    have hξ : ξ ≠ 0 := smul_ne_zero (ne_of_gt (zero_lt_one.trans_le (hw i j.1 j.2)))
      ((Q i j.1).nonzero j.2)
    obtain ⟨W,hW,hKW,hWmargin⟩ := hmargin ((Q i j.1).Q j.2) (hQ i j.1 j.2)
      (A.tensorPlaneRead i g.inner) (A.tensorPlaneRead_metric_smooth g i).continuous
      (hup i j.1 j.2) (modeSupport (K i j)) (hlow i j.1 j.2)
    let f : SupportedField (F := ℝ) (modeSupport (K i j)) :=
      (w i j.1 j.2)⁻¹ • A.exactCellCutoff i (pow_pos hz 6) (hcover i) j.1.val
    have hP (m : ℕ) : 1 ≤ L m/z^(6*m) :=
      (one_le_div (pow_pos hz _)).mpr ((pow_le_one₀ hz.le hz1).trans (hL m))
    obtain ⟨V,hV,c,d,_,hcC,hcJ,hcD,hψ,hform,hbudget⟩ := hmean
      (A.jetChartMap_smooth i hF) (K i j) hξ hW hKW (hU₀ i) (K₀ i) (hUK i)
      ((A.cellChartCompact_subset i (a i) (z^6) j.1.val).trans (hKU i)) hD
      (by simpa only [A.jetChartMap_plane] using fun x hx => (hgeom i j.1 j.2 x hx).1)
      (by simpa only [A.jetChartMap_plane] using fun x hx => (hgeom i j.1 j.2 x hx).2.1)
      (by simpa only [A.jetChartMap_plane] using fun x hx => (hgeom i j.1 j.2 x hx).2.2.1)
      (by simpa only [A.jetChartMap_plane] using fun x hx => (hgeom i j.1 j.2 x hx).2.2.2)
      ((Q i j.1).Q j.2) hWmargin τ s hs hs1 B (fun m => L m/z^(6*m)) hB hP
      (fun m => ⟨(hBD m).1,(hphase i j.1 j.2 m).1,(hphase i j.1 j.2 m).2 hξ,
        (hQ i j.1 j.2).trans (hBD m).2⟩)
      (by simpa only [A.jetChartMap_plane] using hjets i) f
      (hcut i hz hz1 (hcover i) j.1.val s hs hs1 (w i j.1 j.2) (hw i j.1 j.2))
    exact ⟨c,d,hcC,hcJ,hcD,hψ,hform,hbudget⟩
  choose c d hcC hcJ hcD hψ hform hbudget using local_data
  refine ⟨c,d,fun i j m => ⟨hcC i j m,hcJ i j m,hcD i j m⟩,?_,hform,?_,hbudget⟩
  · intro i j x hx
    rw [hψ i j x hx]
    change (w i j.1 j.2)⁻¹ *
      (A.planeWeight i x * normalizedCutoff (a i) (z^6) j.1.val x) = _
    simp only [supportedCellCutoff_apply,supportedPlaneWeight_apply,div_eq_mul_inv]
    ring
  · intro i j
    exact (A.cellCutoff_tsupport i (pow_pos hz 6) (hcover i) j.1.val).trans (c i j).supportChart

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
