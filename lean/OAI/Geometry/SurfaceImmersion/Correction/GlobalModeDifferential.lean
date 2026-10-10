import OAI.Geometry.SurfaceImmersion.Correction.GlobalOscillatoryModes
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadDifferential

namespace OAI

/-! The actual chart differentials of global oscillatory modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (planeCoordinateIsometry)
open QuadraticMean (realMode realPartCLM)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorChartRead_mode_fderiv {n : ℕ} (i : A.centers) (τ : ℝ)
    {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    fderiv ℝ (A.vectorChartRead i (surfaceMode τ φ Z)) x =
      fderiv ℝ (fun y => realMode (A.vectorChartRead i φ y/τ) (A.vectorChartRead i Z y)) x := by
  ext v : 1
  have hh := congrArg (fun T => T (fun _ : Fin 1 => v)) (A.vectorChartRead_mode_jets i τ hφ hZ 1 hx)
  simpa only [iteratedFDeriv_one_apply] using hh

lemma vectorPlaneRead_mode_fderiv {n : ℕ} (i : A.centers) (τ : ℝ)
    {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z)
    {x : SmallModes.Base}
    (hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    fderiv ℝ (A.vectorPlaneRead i (surfaceMode τ φ Z)) x =
      fderiv ℝ (QuadraticMean.displacement τ (A.vectorPlaneRead i φ) (A.vectorPlaneRead i Z)) x := by
  obtain ⟨y,hy,rfl⟩ := hx
  let f := fun y => realMode (A.vectorChartRead i φ y/τ) (A.vectorChartRead i Z y)
  have hf : ContDiff ℝ ∞ f := (realMode_contDiff τ).comp
    ((A.vectorChartRead_smooth i hφ).prodMk (A.vectorChartRead_smooth i hZ))
  change fderiv ℝ (A.vectorChartRead i (surfaceMode τ φ Z) ∘ planeCoordinateIsometry.symm) _ =
    fderiv ℝ (f ∘ planeCoordinateIsometry.symm) _
  rw [fderiv_comp _ ((A.vectorChartRead_smooth i (surfaceMode_smooth τ hφ hZ)).differentiable
      (by simp) _) (planeCoordinateIsometry.symm.differentiableAt),
    fderiv_comp _ (hf.differentiable (by simp) _) (planeCoordinateIsometry.symm.differentiableAt),
    LinearIsometryEquiv.symm_apply_apply,A.vectorChartRead_mode_fderiv i τ hφ hZ hy]

omit [CompactSpace M] in
lemma vectorPlaneRead_clm {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (i : A.centers)
    (L : V →L[ℝ] W) (F : M → V) :
    A.vectorPlaneRead i (L ∘ F) = L ∘ A.vectorPlaneRead i F := by
  funext x
  change localize (i : M) (A.outer i) (L ∘ F) (planeCoordinateIsometry.symm x) =
    L (localize (i : M) (A.outer i) F (planeCoordinateIsometry.symm x))
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [localize,hx,map_smul]

omit [CompactSpace M] in
lemma vectorPlaneRead_sum {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι] (i : A.centers) (F : ι → M → V) :
    A.vectorPlaneRead i (∑ j, F j) = ∑ j, A.vectorPlaneRead i (F j) := by
  funext x
  simpa only [vectorPlaneRead,vectorChartRead,Function.comp_apply,Finset.sum_apply] using
    congrFun (localize_sum Finset.univ (i : M) (A.outer i) F) (planeCoordinateIsometry.symm x)

omit [CompactSpace M] in
lemma vectorPlaneRead_const_smul {n : ℕ} (i : A.centers) (c : ℂ) (Z : M → Fin n → ℂ) :
    A.vectorPlaneRead i (fun p => c • Z p) = fun x => c • A.vectorPlaneRead i Z x := by
  funext x
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target
  · simp only [vectorPlaneRead,vectorChartRead,localize,Function.comp_apply,indicator_of_mem hx]
    exact smul_comm _ _ _
  · simp only [vectorPlaneRead,vectorChartRead,localize,Function.comp_apply,indicator_of_notMem hx,
      smul_zero]

lemma vectorPlaneRead_modes_fderiv {ι : Type*} [Fintype ι] (i : A.centers) (τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j))
    {x : SmallModes.Base}
    (hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    fderiv ℝ (A.vectorPlaneRead i (∑ j, surfaceMode τ (φ j) (Z j))) x =
      fderiv ℝ (QuadraticMean.sumDisplacement τ
        (fun j => A.vectorPlaneRead i (φ j)) (fun j => A.vectorPlaneRead i (Z j))) x := by
  classical
  rw [A.vectorPlaneRead_sum]
  change fderiv ℝ (∑ j, A.vectorPlaneRead i (surfaceMode τ (φ j) (Z j))) x =
    fderiv ℝ (fun y => ∑ j, QuadraticMean.displacement τ (A.vectorPlaneRead i (φ j))
      (A.vectorPlaneRead i (Z j)) y) x
  have he : (∑ j, A.vectorPlaneRead i (surfaceMode τ (φ j) (Z j))) =
      fun y => ∑ j, A.vectorPlaneRead i (surfaceMode τ (φ j) (Z j)) y := by
    funext y
    exact Finset.sum_apply _ _ _
  have hloc (j : ι) : DifferentiableAt ℝ (QuadraticMean.displacement τ
      (A.vectorPlaneRead i (φ j)) (A.vectorPlaneRead i (Z j))) x :=
    ((realMode_contDiff τ).comp ((A.vectorPlaneRead_smooth i (hφ j)).prodMk
      (A.vectorPlaneRead_smooth i (hZ j)))).differentiable (by simp) x
  rw [he,fderiv_fun_sum (fun j _ =>
    (A.vectorPlaneRead_smooth i (surfaceMode_smooth τ (hφ j) (hZ j))).differentiable (by simp) x),
    fderiv_fun_sum (fun j _ => hloc j)]
  apply Finset.sum_congr rfl
  intro j _
  exact A.vectorPlaneRead_mode_fderiv i τ (hφ j) (hZ j) hx

lemma vectorPlaneRead_modes_metric {ι : Type*} [Fintype ι] [DecidableEq ι] (i : A.centers) (τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j))
    {x : SmallModes.Base}
    (hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    RealModes.realMetricTensor (A.vectorPlaneRead i (∑ j, surfaceMode τ (φ j) (Z j))) x =
      RealModes.zeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
        (fun j => A.vectorPlaneRead i (Z j)) x +
      RealModes.nonzeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
        (fun j => A.vectorPlaneRead i (Z j)) x := by
  classical
  have hd := A.vectorPlaneRead_modes_fderiv i τ φ Z hφ hZ hx
  have he : RealModes.realMetricTensor (A.vectorPlaneRead i (∑ j, surfaceMode τ (φ j) (Z j))) x =
      RealModes.realMetricTensor (QuadraticMean.sumDisplacement τ
        (fun j => A.vectorPlaneRead i (φ j)) (fun j => A.vectorPlaneRead i (Z j))) x := by
    ext k
    simp only [RealModes.realMetricTensor_apply, RealModes.realMetric,SmallModes.coordDeriv,hd]
  rw [he]
  exact RealModes.realMetric_sumDisplacement
    (fun j => (A.vectorPlaneRead_smooth i (hφ j)).differentiable (by simp) x)
    (fun j => (A.vectorPlaneRead_smooth i (hZ j)).differentiable (by simp) x) τ

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
