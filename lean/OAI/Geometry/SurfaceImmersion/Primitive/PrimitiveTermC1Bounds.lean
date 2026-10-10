import OAI.Geometry.SurfaceImmersion.Atlas.PhaseCovectorFamily
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPrimitiveFamily
import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasTensorBounds

namespace OAI

/-! Actual primitive tensor terms have a uniform C1 bound from their scalar
amplitude and phase-covector coordinate bounds. All constants precede those
functions and every later cycle count. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
local instance termBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance termBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance termBoundDualNormed : NormedAddCommGroup (Plane →L[ℝ] ℝ) := inferInstance
local instance termBoundDualSpace : NormedSpace ℝ (Plane →L[ℝ] ℝ) := inferInstance

private abbrev PrimitiveLocalData := ℝ × (ℝ × (Plane →L[ℝ] ℝ))
private def primitiveLocalPolynomial (z : PrimitiveLocalData) : TensorFiber :=
  (z.1^2*z.2.1^2) • z.2.2.smulRight z.2.2

private lemma primitiveLocalPolynomial_smooth : ContDiff ℝ ∞ primitiveLocalPolynomial := by
  unfold primitiveLocalPolynomial
  exact ((contDiff_fst.pow 2).mul (contDiff_snd.fst.pow 2)).smul
    (contDiff_snd.snd.smulRight contDiff_snd.snd)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance termBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance termBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance termBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance termBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

omit [CompactSpace M] in
lemma primitive_term_localized (amp phi : M → ℝ)
    (hphi : ContMDiff planeModel 𝓘(ℝ) ∞ phi) (i : B.centers)
    {y : JetPolynomial.Base} (hy : y ∈ (chart (i : M)).target) :
    B.bundleLocalize B.tensorTriv i
      (fun p => (amp p)^2 • phaseDifferentialSquare phi p) y =
      primitiveLocalPolynomial (B.chartWeight i y,
        (amp ((chart (i : M)).symm y),B.phaseCovectorRead i phi y)) := by
  let p := (chart (i : M)).symm y
  have hp : p ∈ (chart (i : M)).source := (chart (i : M)).map_target hy
  have hpy : chart (i : M) p = y := (chart (i : M)).right_inv hy
  change (chart (i : M)).target.indicator (fun x => (B.weight i ((chart (i : M)).symm x))^2 •
    (B.tensorTriv i).continuousLinearMapAt ℝ ((chart (i : M)).symm x)
      ((amp ((chart (i : M)).symm x))^2 • phaseDifferentialSquare phi ((chart (i : M)).symm x))) y = _
  rw [indicator_of_mem hy,map_smul,smul_smul]
  change (B.weight i p^2*amp p^2) •
    (B.tensorTriv i).continuousLinearMapAt ℝ p (phaseDifferentialSquare phi p) = _
  unfold phaseDifferentialSquare
  erw [B.tensor_frame_square i hp,B.covectorFrame_mfderiv phi hphi i hp,hpy]
  simp only [primitiveLocalPolynomial,chartWeight,indicator_of_mem hy]
  rfl

/-- A bound on the actual coordinate amplitude and covector, including
one derivative, controls the genuine globally supported primitive term. -/
theorem primitive_term_tensor_C1_bound {D : ℝ} (hD : 0 ≤ D) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ amp phi : M → ℝ,
      ContMDiff planeModel 𝓘(ℝ) ∞ amp → ContMDiff planeModel 𝓘(ℝ) ∞ phi →
      (∀ i p, p ∈ tsupport (B.weight i) →
        |amp p| ≤ D ∧ ‖fderiv ℝ (amp ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ D) →
      (∀ i y, y ∈ (B.chartWeightCompact i : Set JetPolynomial.Base) →
        ‖B.phaseCovectorRead i phi y‖ ≤ D ∧
          ‖fderiv ℝ (B.phaseCovectorRead i phi) y‖ ≤ D) →
      B.TensorWeightedBound 1 1 E (fun p => (amp p)^2 • phaseDifferentialSquare phi p) := by
  classical
  have hwcompact (i : B.centers) : HasCompactSupport (B.chartWeight i) :=
    (B.chartWeightCompact i).isCompact.of_isClosed_subset (isClosed_tsupport _)
      (B.supportedChartWeight i).tsupport_subset
  choose W hW hw using fun i => compact_smooth_bound (B.chartWeight_smooth i) (hwcompact i) 1
  let R : ℝ := 1+D+∑ i : B.centers, W i
  have hsum : 0 ≤ ∑ i : B.centers, W i := Finset.sum_nonneg (fun i _ => hW i)
  have hR : 1 ≤ R := by dsimp only [R]; linarith
  have hDR : D ≤ R := by dsimp only [R]; linarith
  have hWR (i : B.centers) : W i ≤ R := by
    have hh := Finset.single_le_sum (fun j _ => hW j) (Finset.mem_univ i)
    dsimp only [R]
    linarith
  obtain ⟨K,hK,hpoly⟩ := compact_coefficient_bound uniqueDiffOn_univ
    (isCompact_closedBall (0 : PrimitiveLocalData) R) (subset_univ _)
    primitiveLocalPolynomial_smooth.contDiffOn 1
  refine ⟨K*R,mul_nonneg (zero_le_one.trans hK) (zero_le_one.trans hR),?_⟩
  intro amp phi hamp hphi hampBound hphiBound
  let T : ∀ p : M, CovariantTwoTensor p := fun p => (amp p)^2 • phaseDifferentialSquare phi p
  have hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p)) :=
    (hamp.pow 2).smul_section (B.phaseDifferentialSquare_smooth phi hphi)
  have hpoint (i : B.centers) (y : JetPolynomial.Base)
      (hy : y ∈ (B.chartWeightCompact i : Set JetPolynomial.Base)) :
      ‖B.bundleLocalize B.tensorTriv i T y‖ ≤ K*R ∧
      ‖fderiv ℝ (B.bundleLocalize B.tensorTriv i T) y‖ ≤ K*R := by
    rcases hy with ⟨p,hp,rfl⟩
    have hpS := B.weight_support i hp
    have hyT := (chart (i : M)).map_source hpS
    let a : JetPolynomial.Base → ℝ := amp ∘ (chart (i : M)).symm
    let v : JetPolynomial.Base → Plane →L[ℝ] ℝ := B.phaseCovectorRead i phi
    let X : JetPolynomial.Base → PrimitiveLocalData := fun x => (B.chartWeight i x,(a x,v x))
    have ha : ContDiffAt ℝ ∞ a (chart (i : M) p) :=
      ((hamp.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn).contDiffAt
        ((chart (i : M)).open_target.mem_nhds hyT)
    have hv : ContDiffAt ℝ ∞ v (chart (i : M) p) :=
      (B.phaseCovectorRead_smoothOn i phi hphi).contDiffAt
        ((chart (i : M)).open_target.mem_nhds hyT)
    have hw' := (B.chartWeight_smooth i).contDiffAt (x := chart (i : M) p)
    have hX : ContDiffAt ℝ ∞ X (chart (i : M) p) := hw'.prodMk (ha.prodMk hv)
    have haw := hampBound i p hp
    have hvw := hphiBound i (chart (i : M) p) ⟨p,hp,rfl⟩
    have hweight : ‖B.chartWeight i (chart (i : M) p)‖ ≤ R :=
      ((hw i).norm_le (mem_univ _)).trans (hWR i)
    have hweightD : ‖fderiv ℝ (B.chartWeight i) (chart (i : M) p)‖ ≤ R := by
      have hh := (hw i).deriv_le zero_lt_one le_rfl (mem_univ (chart (i : M) p))
      simp only [iteratedFDerivWithin_univ,one_pow,div_one,norm_iteratedFDeriv_one] at hh
      exact hh.trans (hWR i)
    have ha0 : ‖a (chart (i : M) p)‖ ≤ R := by
      simpa only [a,Function.comp_apply,(chart (i : M)).left_inv hpS,Real.norm_eq_abs] using haw.1.trans hDR
    have hXnorm : ‖X (chart (i : M) p)‖ ≤ R := by
      simpa only [X,Prod.norm_def,max_le_iff] using
        And.intro hweight (And.intro ha0 (hvw.1.trans hDR))
    have hDX : ‖fderiv ℝ X (chart (i : M) p)‖ ≤ R := by
      rw [((hw'.differentiableAt (by simp)).hasFDerivAt.prodMk
        ((ha.differentiableAt (by simp)).hasFDerivAt.prodMk
          (hv.differentiableAt (by simp)).hasFDerivAt)).fderiv]
      simp only [ContinuousLinearMap.opNorm_prod,Prod.norm_def,max_le_iff]
      exact ⟨hweightD,haw.2.trans hDR,hvw.2.trans hDR⟩
    have hball : X (chart (i : M) p) ∈ Metric.closedBall (0 : PrimitiveLocalData) R := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hXnorm
    have hvalue : ‖primitiveLocalPolynomial (X (chart (i : M) p))‖ ≤ K := by
      simpa only [iteratedFDerivWithin_univ,norm_iteratedFDeriv_zero] using hpoly 0 (by omega) _ hball
    have hderiv : ‖fderiv ℝ primitiveLocalPolynomial (X (chart (i : M) p))‖ ≤ K := by
      simpa only [iteratedFDerivWithin_univ,norm_iteratedFDeriv_one] using hpoly 1 le_rfl _ hball
    have he : B.bundleLocalize B.tensorTriv i T =ᶠ[𝓝 (chart (i : M) p)]
        primitiveLocalPolynomial ∘ X := by
      filter_upwards [(chart (i : M)).open_target.mem_nhds hyT] with x hx
      exact B.primitive_term_localized amp phi hphi i hx
    refine ⟨?_,?_⟩
    · rw [he.self_of_nhds]
      exact hvalue.trans (le_mul_of_one_le_right (zero_le_one.trans hK) hR)
    · rw [he.fderiv_eq,fderiv_comp (chart (i : M) p)
        (primitiveLocalPolynomial_smooth.differentiable (by simp) _)
        (hX.differentiableAt (by simp))]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hderiv hDX (norm_nonneg _) (zero_le_one.trans hK))
  intro i j hj y _
  simp only [one_pow,one_mul,iteratedFDerivWithin_univ]
  by_cases hy : y ∈ (B.chartWeightCompact i : Set JetPolynomial.Base)
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · simpa only [norm_iteratedFDeriv_zero] using (hpoint i y hy).1
    · simpa only [norm_iteratedFDeriv_one] using (hpoint i y hy).2
  · have hz : iteratedFDeriv ℝ j (B.bundleLocalize B.tensorTriv i T) y = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hh
      exact hy ((localize_tsupport (i : M) (B.weight_support i) _)
        (tsupport_iteratedFDeriv_subset j hh))
    rw [hz,norm_zero]
    exact mul_nonneg (zero_le_one.trans hK) (zero_le_one.trans hR)

/-- The same primitive bound is measured in any fixed background atlas. -/
theorem primitive_term_background_C1_bound (A : SmoothingAtlas M) {D : ℝ} (hD : 0 ≤ D) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ amp phi : M → ℝ,
      ContMDiff planeModel 𝓘(ℝ) ∞ amp → ContMDiff planeModel 𝓘(ℝ) ∞ phi →
      (∀ i p, p ∈ tsupport (B.weight i) →
        |amp p| ≤ D ∧ ‖fderiv ℝ (amp ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ D) →
      (∀ i y, y ∈ (B.chartWeightCompact i : Set JetPolynomial.Base) →
        ‖B.phaseCovectorRead i phi y‖ ≤ D ∧
          ‖fderiv ℝ (B.phaseCovectorRead i phi) y‖ ≤ D) →
      A.TensorWeightedBound 1 1 E (fun p => (amp p)^2 • phaseDifferentialSquare phi p) := by
  obtain ⟨E,hE,hbound⟩ := B.primitive_term_tensor_C1_bound hD
  obtain ⟨C,hC,hchange⟩ := B.tensorWeightedBound_change_atlas A 1
  refine ⟨C*E,mul_nonneg hC hE,?_⟩
  intro amp phi hamp hphi ha hp
  exact hchange _ 1 E zero_lt_one le_rfl hE
    ((hamp.pow 2).smul_section (B.phaseDifferentialSquare_smooth phi hphi))
    (hbound amp phi hamp hphi ha hp)

end SmoothingAtlas

namespace SmoothPrimitiveFamily
variable {ι : Type*} [Fintype ι] {u : ∀ p : M, CovariantTwoTensor p}

/-- A single bound works for every term of every family with these actual
coordinate amplitude and phase-covector estimates. -/
theorem term_background_C1_bound (B A : SmoothingAtlas M) {D : ℝ} (hD : 0 ≤ D) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ d : SmoothPrimitiveFamily ι u,
      (∀ a i p, p ∈ tsupport (B.weight i) →
        |d.amplitude a p| ≤ D ∧
          ‖fderiv ℝ (d.amplitude a ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ D) →
      (∀ a i y, y ∈ (B.chartWeightCompact i : Set JetPolynomial.Base) →
        ‖B.phaseCovectorRead i (d.phase a) y‖ ≤ D ∧
          ‖fderiv ℝ (B.phaseCovectorRead i (d.phase a)) y‖ ≤ D) →
      ∀ a, A.TensorWeightedBound 1 1 E (d.term a) := by
  obtain ⟨E,hE,hbound⟩ := B.primitive_term_background_C1_bound A hD
  exact ⟨E,hE,fun d ha hp a => hbound (d.amplitude a) (d.phase a)
    (d.smoothAmplitude a) (d.smoothPhase a) (ha a) (hp a)⟩

end SmoothPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
