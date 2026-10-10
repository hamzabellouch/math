import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.Nonneg
import OAI.Analysis.CoulombIonization.ThomasFermi.TfPotential

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace CoulombAnalysis

def coulombNear : TFSpace → ℝ := (ball 0 1).indicator (fun x => ‖x‖⁻¹ - 1)
def coulombFar (x : TFSpace) : ℝ := (max ‖x‖ 1)⁻¹

lemma coulombNear_memLp : MemLp coulombNear (5 / 2) := by
  rw [coulombNear, memLp_indicator_iff_restrict measurableSet_ball]
  exact (nuclear_memLp 1).sub (memLp_const 1)

lemma coulombFar_bound (x : TFSpace) : ‖coulombFar x‖ ≤ 1 := by
  rw [coulombFar, norm_inv, Real.norm_of_nonneg (le_trans (by norm_num) (le_max_right _ _))]
  exact inv_le_one_of_one_le₀ (le_max_right _ _)

lemma coulombFar_continuous : Continuous coulombFar := by
  exact (continuous_norm.max continuous_const).inv₀ (fun x =>
    ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_right ‖x‖ 1)))

lemma coulomb_decompose (x : TFSpace) : ‖x‖⁻¹ = coulombNear x + coulombFar x := by
  by_cases hx : ‖x‖ < 1
  · simp only [coulombNear, indicator_of_mem (mem_ball_zero_iff.mpr hx), coulombFar,
      max_eq_right hx.le, inv_one]
    ring
  · simp only [coulombNear, indicator_of_notMem (mt mem_ball_zero_iff.mp hx), coulombFar,
      max_eq_left (le_of_not_gt hx), zero_add]

def tfSubMap (x : TFSpace) : C(TFSpace, TFSpace) := ⟨fun y => x - y, continuous_const.sub continuous_id⟩
lemma tfSubMap_preserving (x : TFSpace) : MeasurePreserving (tfSubMap x) volume volume :=
  volume.measurePreserving_sub_left x

lemma tfSubMap_continuous : Continuous tfSubMap := by
  exact (⟨fun p : TFSpace × TFSpace => p.1 - p.2, continuous_fst.sub continuous_snd⟩ :
    C(TFSpace × TFSpace, TFSpace)).curry.continuous

def coulombNearLp : Lp ℝ (5 / 2) (volume : Measure TFSpace) := coulombNear_memLp.toLp coulombNear

def coulombNearTranslate (x : TFSpace) : Lp ℝ (5 / 2) (volume : Measure TFSpace) :=
  Lp.compMeasurePreserving (tfSubMap x) (tfSubMap_preserving x) coulombNearLp

lemma coulombNearTranslate_coe (x : TFSpace) :
    coulombNearTranslate x =ᵐ[volume] fun y => coulombNear (x - y) := by
  exact (Lp.coeFn_compMeasurePreserving coulombNearLp (tfSubMap_preserving x)).trans
    ((tfSubMap_preserving x).quasiMeasurePreserving.ae coulombNear_memLp.coeFn_toLp)

lemma coulombNearTranslate_continuous : Continuous coulombNearTranslate := by
  exact continuous_const.compMeasurePreservingLp tfSubMap_continuous tfSubMap_preserving
    (ENNReal.div_ne_top (by norm_num) (by norm_num))

lemma coulombNearMultiply_integrable {ρ : TFSpace → ℝ} (hρ : MemLp ρ (5 / 3)) (x : TFSpace) :
    Integrable (fun y => coulombNear (x - y) * ρ y) := by
  exact (coulombNear_memLp.comp_measurePreserving (tfSubMap_preserving x)).integrable_mul hρ

lemma coulombFarMultiply_integrable {ρ : TFSpace → ℝ} (hρ : Integrable ρ) (x : TFSpace) :
    Integrable (fun y => coulombFar (x - y) * ρ y) := by
  apply hρ.bdd_mul (coulombFar_continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Eventually.of_forall fun y => coulombFar_bound (x - y)

lemma tfPotential_integrable {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    (x : TFSpace) : Integrable (fun y => ρ y / ‖x - y‖) := by
  have hsum := (coulombNearMultiply_integrable hp x).add (coulombFarMultiply_integrable h1 x)
  convert! hsum using 1
  ext y
  dsimp
  rw [div_eq_mul_inv, coulomb_decompose]
  ring

lemma tfPotential_continuous {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3)) :
    Continuous (tfPotential ρ) := by
  have hnear : Continuous (fun x => ∫ y, coulombNear (x - y) * ρ y) := by
    let pair := (ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume : Measure TFSpace) (5 / 2) (5 / 3)
    have hc := (pair.flip (hp.toLp ρ)).continuous.comp coulombNearTranslate_continuous
    convert! hc using 1
    ext x
    dsimp only [Function.comp_apply, pair, ContinuousLinearMap.flip_apply]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [coulombNearTranslate_coe x, hp.coeFn_toLp] with y hy hρy
    simp only [ContinuousLinearMap.mul_apply', hy, hρy]
  have hfar : Continuous (fun x => ∫ y, ρ y * coulombFar (x - y)) := by
    have hc := (show BddAbove (range fun x => ‖coulombFar x‖) from
      ⟨1, by rintro _ ⟨x, rfl⟩; exact coulombFar_bound x⟩).continuous_convolution_right_of_integrable
        (ContinuousLinearMap.mul ℝ ℝ) h1 coulombFar_continuous
    exact hc
  convert! hnear.add hfar using 1
  ext x
  dsimp only [Pi.add_apply]
  rw [← integral_add (coulombNearMultiply_integrable hp x)
    ((coulombFarMultiply_integrable h1 x).congr (Eventually.of_forall fun y => mul_comm _ _))]
  apply integral_congr_ae (Eventually.of_forall fun y => ?_)
  rw [div_eq_mul_inv, coulomb_decompose]
  ring

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution

namespace CoulombAnalysis

def newtonMul : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
def newtonMul₁ : ℝ →L[ℝ] (TFSpace →L[ℝ] ℝ) →L[ℝ] (TFSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.precompR TFSpace newtonMul
lemma fderiv_apply_const_scalar {f : TFSpace → ℝ} {x : TFSpace}
    (hd : DifferentiableAt ℝ (fderiv ℝ f) x) (u v : TFSpace) :
    fderiv ℝ (fun z => fderiv ℝ f z v) x u = fderiv ℝ (fderiv ℝ f) x u v := by
  simp only [fderiv_clm_apply hd (differentiableAt_const v), fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

lemma fderiv_convolution_eval {ρ K : TFSpace → ℝ} (hρ : LocallyIntegrable ρ volume)
    (hK : HasCompactSupport K) (hd : ContDiff ℝ 1 K) (x u : TFSpace) :
    fderiv ℝ (ρ ⋆[newtonMul] K) x u = ∫ y, ρ y * fderiv ℝ K (x - y) u := by
  rw [(hK.hasFDerivAt_convolution_right newtonMul hρ hd x).fderiv]
  have hi := (hK.fderiv ℝ).convolutionExists_right newtonMul₁ hρ
    (hd.continuous_fderiv (by norm_num)) x
  change (∫ t, newtonMul₁ (ρ t) (fderiv ℝ K (x - t))) u = _
  rw [ContinuousLinearMap.integral_apply hi.integrable u]
  rfl

lemma second_fderiv_convolution {ρ K : TFSpace → ℝ} (hρ : LocallyIntegrable ρ volume)
    (hK : HasCompactSupport K) (hd : ContDiff ℝ 2 K) (x u v : TFSpace) :
    fderiv ℝ (fderiv ℝ (ρ ⋆[newtonMul] K)) x u v =
      ∫ y, ρ y * (fderiv ℝ (fderiv ℝ K) (x - y) u v) := by
  have hc : ContDiff ℝ 2 (ρ ⋆[newtonMul] K) := hK.contDiff_convolution_right newtonMul hρ hd
  have hc' := (hc.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  rw [← fderiv_apply_const_scalar hc'.differentiableAt u v]
  have he : (fun z => fderiv ℝ (ρ ⋆[newtonMul] K) z v) =
      ρ ⋆[newtonMul] (fun z => fderiv ℝ K z v) := by
    funext z
    exact fderiv_convolution_eval hρ hK (hd.of_le (by norm_num)) z v
  rw [he]
  have hdk : ContDiff ℝ 1 (fun z => fderiv ℝ K z v) :=
    (hd.fderiv_right (by norm_num)).clm_apply contDiff_const
  rw [fderiv_convolution_eval hρ (hK.fderiv_apply ℝ v) hdk]
  apply integral_congr_ae (Eventually.of_forall fun y => ?_)
  rw [fderiv_apply_const_scalar ((hd.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)).differentiableAt]

lemma second_kernel_integrable {ρ K : TFSpace → ℝ} (hρ : LocallyIntegrable ρ volume)
    (hK : HasCompactSupport K) (hd : ContDiff ℝ 2 K) (x u v : TFSpace) :
    Integrable (fun y => ρ y * (fderiv ℝ (fderiv ℝ K) (x - y) u v)) := by
  have hdk : ContDiff ℝ 1 (fun z => fderiv ℝ K z v) :=
    (hd.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hc : Continuous (fun z => fderiv ℝ (fun w => fderiv ℝ K w v) z u) :=
    (hdk.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi := ((hK.fderiv_apply ℝ v).fderiv_apply ℝ u).convolutionExists_right newtonMul hρ hc x
  convert! hi.integrable using 1
  ext y
  exact (congrArg (ρ y * ·) (fderiv_apply_const_scalar
    ((hd.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable
      (by norm_num)).differentiableAt u v)).symm

lemma laplacian_convolution {ρ K : TFSpace → ℝ} (hρ : LocallyIntegrable ρ volume)
    (hK : HasCompactSupport K) (hd : ContDiff ℝ 2 K) (x : TFSpace) :
    Δ (ρ ⋆[newtonMul] K) x = ∫ y, ρ y * Δ K (x - y) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp_rw [second_fderiv_convolution hρ hK hd, Finset.mul_sum]
  rw [integral_finsetSum]
  exact fun i _ => second_kernel_integrable hρ hK hd x _ _

def annularCoulomb (a b : ContDiffBump (0 : TFSpace)) (x : TFSpace) : ℝ :=
  (1 - a x) * b x * ‖x‖⁻¹

lemma annularCoulomb_compact (a b : ContDiffBump (0 : TFSpace)) :
    HasCompactSupport (annularCoulomb a b) := by
  exact b.hasCompactSupport.mul_left.mul_right

lemma annularCoulomb_smooth (a b : ContDiffBump (0 : TFSpace)) :
    ContDiff ℝ 2 (annularCoulomb a b) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [a.eventuallyEq_one] with x hx
    simp [annularCoulomb, hx]
  · have hn : ContDiffAt ℝ 2 (fun x : TFSpace => ‖x‖⁻¹) x :=
      contDiffAt_norm ℝ hx |>.inv (norm_ne_zero_iff.mpr hx)
    exact ((contDiffAt_const.sub a.contDiff.contDiffAt).mul b.contDiff.contDiffAt).mul hn

lemma annularCoulomb_eq (a b : ContDiffBump (0 : TFSpace)) {x : TFSpace}
    (ha : a.rOut ≤ ‖x‖) (hb : ‖x‖ ≤ b.rIn) : annularCoulomb a b x = ‖x‖⁻¹ := by
  simp [annularCoulomb, a.zero_of_le_dist (by simpa using ha),
    b.one_of_mem_closedBall (by simpa using hb)]

lemma annularCoulomb_eventually (a b : ContDiffBump (0 : TFSpace)) {x : TFSpace}
    (ha : a.rOut < ‖x‖) (hb : ‖x‖ < b.rIn) :
    annularCoulomb a b =ᶠ[𝓝 x] fun z => ‖z‖⁻¹ := by
  filter_upwards [continuous_norm.continuousAt.eventually (Ioo_mem_nhds ha hb)] with z hz
  exact annularCoulomb_eq a b hz.1.le hz.2.le

lemma annularCoulomb_laplacian (a b : ContDiffBump (0 : TFSpace)) {x : TFSpace}
    (ha : a.rOut < ‖x‖) (hb : ‖x‖ < b.rIn) : Δ (annularCoulomb a b) x = 0 := by
  have hx : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (a.rOut_pos.trans ha))
  have he := annularCoulomb_eventually a b ha hb
  rw [(laplacian_congr_nhds he).eq_of_nhds]
  have heq : (fun z : TFSpace => ‖z‖⁻¹) = CoulombPDE.radialPower (-(1 / 2)) :=
    funext fun z => (CoulombPDE.radialPower_half_inv z).symm
  rw [heq, CoulombPDE.radial_laplacian_three (-(1 / 2)) hx]
  norm_num

theorem tfPotential_harmonic_separated {ρ : TFSpace → ℝ} (hρ : LocallyIntegrable ρ volume)
    {x : TFSpace} {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hs : ∀ y, ρ y ≠ 0 → a ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ b) :
    ContDiffAt ℝ 2 (tfPotential ρ) x ∧ Δ (tfPotential ρ) x = 0 := by
  let ai : ContDiffBump (0 : TFSpace) := ⟨a / 4, a / 2, by positivity, by linarith⟩
  let bo : ContDiffBump (0 : TFSpace) := ⟨b + 1, b + 2, by positivity, by linarith⟩
  let K := annularCoulomb ai bo
  have hk := annularCoulomb_compact ai bo
  have hdk := annularCoulomb_smooth ai bo
  have he : tfPotential ρ =ᶠ[𝓝 x] (ρ ⋆[newtonMul] K) := by
    filter_upwards [ball_mem_nhds x (show 0 < min (a / 4) (1 / 2 : ℝ) by positivity)] with z hz
    apply integral_congr_ae (Eventually.of_forall fun y => ?_)
    change ρ y / ‖z - y‖ = ρ y * K (z - y)
    by_cases hy : ρ y = 0
    · simp [hy]
    · obtain ⟨hlo, hhi⟩ := hs y hy
      have hz₁ : dist z x < a / 4 := lt_of_lt_of_le hz (min_le_left _ _)
      have hz₂ : dist z x < 1 / 2 := lt_of_lt_of_le hz (min_le_right _ _)
      have hu := dist_triangle z x y
      have hl := dist_triangle x z y
      rw [dist_comm x z] at hl
      simp only [dist_eq_norm] at hz₁ hz₂ hu hl
      have hka : ai.rOut ≤ ‖z - y‖ := by dsimp [ai]; linarith
      have hkb : ‖z - y‖ ≤ bo.rIn := by dsimp [bo]; linarith
      rw [show K (z - y) = ‖z - y‖⁻¹ from annularCoulomb_eq ai bo hka hkb, div_eq_mul_inv]
  refine ⟨(hk.contDiff_convolution_right newtonMul hρ hdk).contDiffAt.congr_of_eventuallyEq he, ?_⟩
  rw [(laplacian_congr_nhds he).eq_of_nhds, laplacian_convolution hρ hk hdk]
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun y => by
    change ρ y * Δ K (x - y) = 0
    by_cases hy : ρ y = 0
    · simp [hy]
    · obtain ⟨hlo, hhi⟩ := hs y hy
      have hka : ai.rOut < ‖x - y‖ := by dsimp [ai]; linarith
      have hkb : ‖x - y‖ < bo.rIn := by dsimp [bo]; linarith
      rw [show Δ K (x - y) = 0 from annularCoulomb_laplacian ai bo hka hkb, mul_zero]

end CoulombAnalysis

open scoped RealInnerProductSpace

lemma exists_orthogonal_map_norm_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (h : ‖x‖ = ‖y‖) : ∃ e : E ≃ₗᵢ[ℝ] E, e x = y := by
  by_cases hxy : x + y = 0
  · refine ⟨LinearIsometryEquiv.neg ℝ, ?_⟩
    change -x = y
    exact neg_eq_iff_add_eq_zero.mpr hxy
  · refine ⟨(ℝ ∙ (x + y)).reflection, ?_⟩
    rw [Submodule.reflection_singleton_apply]
    have hn : ‖x + y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hxy)
    have he : (2 : ℝ) * (inner ℝ (x + y) x / ‖x + y‖ ^ 2) = 1 := by
      rw [← mul_div_assoc]
      apply (div_eq_one_iff_eq hn).mpr
      rw [inner_add_left, real_inner_self_eq_norm_sq, real_inner_comm x y,
        norm_add_sq_real, h]
      ring
    rw [two_smul, ← add_smul, ← two_mul]
    change (2 * (inner ℝ (x + y) x / ‖x + y‖ ^ 2)) • (x + y) - x = y
    rw [he, one_smul]
    abel

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

end

end OAI
