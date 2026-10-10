import OAI.Geometry.Perimeter.Regularity.SmoothSublevelPairingBound

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack
open RPI.Boundary

def rankOneNormalError {n : ℕ} (E : Set (Euc n)) (φ : Euc n → ℝ)
    (v : Euc n) (x : Euc n) : Euc n :=
  (fderiv ℝ φ x v) • approximateNormal E x -
    (inner ℝ (approximateNormal E x) v) • gradient φ x

theorem inner_rankOnePiola {n : ℕ} (E : Set (Euc n)) (φ : Euc n → ℝ)
    (v : Euc n) (t : ℝ) (W : Euc n → Euc n) (x : Euc n) :
    inner ℝ (approximateNormal E x) (rankOnePiola φ v t W x) =
      inner ℝ (approximateNormal E x + t • rankOneNormalError E φ v x)
        (W (rankOneVariation φ v t x)) := by
  simp only [rankOnePiola, rankOneNormalError, rankOneJacobian, inner_sub_right,
    real_inner_smul_right, inner_add_left, real_inner_smul_left, inner_sub_left,
    inner_gradient_left]
  ring

theorem rankOneNormalError_norm_le {n : ℕ} (E : Set (Euc n)) {φ : Euc n → ℝ}
    {L : ℝ≥0} (hL : LipschitzWith L φ) (v x : Euc n) :
    ‖rankOneNormalError E φ v x‖ ≤ 2 * L * ‖v‖ := by
  have hD : ‖fderiv ℝ φ x‖ ≤ L := norm_fderiv_le_of_lipschitz ℝ hL
  have hN := approximateNormal_norm_le_one E x
  have hgrad : ‖gradient φ x‖ ≤ L := by simpa only [gradient, LinearIsometryEquiv.norm_map] using hD
  have hDv : ‖fderiv ℝ φ x v‖ ≤ L * ‖v‖ :=
    ((fderiv ℝ φ x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg v))
  have hNv : ‖inner ℝ (approximateNormal E x) v‖ ≤ ‖v‖ :=
    (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg v])
  calc
    _ ≤ ‖(fderiv ℝ φ x v) • approximateNormal E x‖ +
        ‖(inner ℝ (approximateNormal E x) v) • gradient φ x‖ := norm_sub_le _ _
    _ ≤ L * ‖v‖ * 1 + ‖v‖ * L := by
      simp only [norm_smul]
      exact add_le_add (mul_le_mul hDv hN (norm_nonneg _) (by positivity))
        (mul_le_mul hNv hgrad (norm_nonneg _) (norm_nonneg v))
    _ = _ := by ring

theorem perimeter_image_rankOneVariation_le {n : ℕ} (hn : 1 < n)
    {E U : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hU : IsOpen U) (hP : perimeter E U ≠ ⊤)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφU : tsupport φ ⊆ U)
    {L : ℝ≥0} (hL : LipschitzWith L φ) (v : Euc n) (t : ℝ)
    (ht : ‖t‖ * L * ‖v‖ < 1) :
    perimeter (rankOneVariation φ v t '' E) U ≤
      ENNReal.ofReal (∫ x in U, ‖approximateNormal E x + t • rankOneNormalError E φ v x‖
        ∂perimeterMeasure E) := by
  obtain ⟨e, he⟩ := exists_rankOneVariation_homeomorph (lt_trans (by norm_num) hn) hL v t ht
  let μ := (perimeterMeasure E).restrict U
  have : IsFiniteMeasure μ := ⟨by rw [Measure.restrict_apply_univ, perimeterMeasure_open E hU]; exact hP.lt_top⟩
  have hmN := (measurable_approximateNormal hmin.1).aestronglyMeasurable (μ := μ)
  have hcgrad : Continuous (gradient φ) := continuous_iff_continuousAt.mpr (fun x ↦
    continuousAt_gradient_of_contDiffAt (hφ.contDiffAt.of_le (by simp)))
  have hmQ : AEStronglyMeasurable (rankOneNormalError E φ v) μ := by
    unfold rankOneNormalError
    exact (((hφ.fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_const).aestronglyMeasurable.smul hmN).sub
      ((hmN.inner (𝕜 := ℝ) (aestronglyMeasurable_const (b := v))).smul hcgrad.aestronglyMeasurable)
  have hiQ : Integrable (rankOneNormalError E φ v) μ :=
    Integrable.of_bound hmQ (2 * L * ‖v‖) (ae_of_all _ (rankOneNormalError_norm_le E hL v))
  have hiN : Integrable (approximateNormal E) μ :=
    Integrable.of_bound hmN 1 (ae_of_all _ (approximateNormal_norm_le_one E))
  have hiA := (hiN.add (hiQ.smul t)).norm
  unfold perimeter
  refine iSup_le fun W ↦ iSup_le fun hW ↦ iSup_le fun hcW ↦ iSup_le fun hWU ↦ iSup_le fun hW1 ↦ ?_
  apply ENNReal.ofReal_le_ofReal
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hmin.1
    (fun x (_ : x ∈ E) ↦ (rankOneVariation_hasFDerivAt (hφ.differentiable (by simp) x) v t).hasFDerivWithinAt)
    (show InjOn (rankOneVariation φ v t) E from by rw [← he]; exact e.injective.injOn)
    (divergence W)
  have hdiv : (∫ x in rankOneVariation φ v t '' E, divergence W x) =
      ∫ x in E, divergence (rankOnePiola φ v t W) x := by
    rw [hchange]
    apply setIntegral_congr_fun hmin.1
    intro x _
    dsimp only
    rw [det_id_add_smulRight]
    change |rankOneJacobian φ v t x| * divergence W (rankOneVariation φ v t x) = _
    rw [abs_of_pos (rankOneJacobian_pos hL v t ht x), divergence_rankOnePiola hφ hW]
  rw [hdiv, minimizing_gaussGreen_local hn hmin U hU hP _
    (rankOnePiola_contDiff hφ hW v t) (rankOnePiola_hasCompactSupport hφ v t e he hcW)
    (rankOnePiola_tsupport_subset_region hφ v t e he hφU hWU)]
  simp_rw [inner_rankOnePiola]
  have hiW : Integrable (fun x ↦ inner ℝ (approximateNormal E x + t • rankOneNormalError E φ v x)
      (W (rankOneVariation φ v t x))) μ := by
    apply Integrable.mono' hiA
    · exact (hmN.add (hmQ.const_smul t)).inner (hW.continuous.comp
        (rankOneVariation_contDiff hφ v t).continuous).aestronglyMeasurable
    · exact ae_of_all _ fun x ↦ (norm_inner_le_norm _ _).trans
        (by simpa only [mul_one, Pi.add_apply, Pi.smul_apply] using mul_le_mul_of_nonneg_left (hW1 _) (norm_nonneg _))
  apply integral_mono_ae hiW hiA
  exact ae_of_all _ fun x ↦ (real_inner_le_norm _ _).trans
    (by simpa only [mul_one, Pi.add_apply, Pi.smul_apply] using mul_le_mul_of_nonneg_left (hW1 _) (norm_nonneg _))

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem norm_unit_add_smul_le_quadratic {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (N Q : V) (hN : ‖N‖ = 1) (t : ℝ) :
    ‖N + t • Q‖ ≤ 1 + t * inner ℝ N Q + (t ^ 2 / 2) * ‖Q‖ ^ 2 := by
  have hs := norm_add_sq_real N (t • Q)
  rw [hN, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_right] at hs
  nlinarith [sq_nonneg (‖N + t • Q‖ - 1)]

theorem linear_term_eq_zero_of_local_quadratic_nonneg (I J : ℝ)
    (h : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ t * I + t ^ 2 * J) : I = 0 := by
  have hm : IsLocalMin (fun t : ℝ ↦ t * I + t ^ 2 * J) 0 := by
    simpa only [IsLocalMin, IsMinFilter, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_add] using h
  have hd : HasDerivAt (fun t : ℝ ↦ t * I + t ^ 2 * J) I 0 := by
    have hh := ((hasDerivAt_id (0 : ℝ)).mul_const I).fun_add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const J)
    simpa using hh
  exact hm.hasDerivAt_eq_zero hd

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack
open RPI.Boundary

theorem minimizing_tangentialGradient_integral_eq_zero_local {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {R : ℝ} (hR : 0 < R) {φ : Euc n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Metric.ball c R) (v : Euc n) :
    (∫ x in Metric.ball c R, inner ℝ (tangentialGradient E φ x) v ∂perimeterMeasure E) = 0 := by
  let U := Metric.ball c R
  let μ := (perimeterMeasure E).restrict U
  have hP : perimeter E U ≠ ⊤ := (hmin.2.1 c R hR).ne
  have : IsFiniteMeasure μ := ⟨by rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]; exact hP.lt_top⟩
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcφ (hφ.of_le (by simp)) one_ne_zero
  let N := approximateNormal E
  let Q := rankOneNormalError E φ v
  let B : ℝ := 2 * L * ‖v‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmN : AEStronglyMeasurable N μ := (measurable_approximateNormal hmin.1).aestronglyMeasurable
  have hcgrad : Continuous (gradient φ) := continuous_iff_continuousAt.mpr (fun x ↦
    continuousAt_gradient_of_contDiffAt (hφ.contDiffAt.of_le (by simp)))
  have hmQ : AEStronglyMeasurable Q μ := by
    dsimp [Q, rankOneNormalError]
    exact (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.smul hmN).sub
      ((hmN.inner (𝕜 := ℝ) (aestronglyMeasurable_const (b := v))).smul hcgrad.aestronglyMeasurable)
  have hN1 : ∀ x, ‖N x‖ ≤ 1 := approximateNormal_norm_le_one E
  have hNu : ∀ᵐ x ∂μ, ‖N x‖ = 1 :=
    (ae_restrict_of_ae (minimizing_halfspaceBlowup_ae hn hmin)).mono fun _ h ↦ h.1
  have hQB : ∀ x, ‖Q x‖ ≤ B := rankOneNormalError_norm_le E hL v
  have hiN : Integrable N μ := Integrable.of_bound hmN 1 (ae_of_all _ hN1)
  have hiQ : Integrable Q μ := Integrable.of_bound hmQ B (ae_of_all _ hQB)
  have hiI : Integrable (fun x ↦ inner ℝ (N x) (Q x)) μ :=
    Integrable.of_bound (hmN.inner hmQ) B (ae_of_all _ fun x ↦
      (norm_inner_le_norm _ _).trans (by nlinarith [hN1 x, hQB x, norm_nonneg (N x), norm_nonneg (Q x)]))
  have hiJ : Integrable (fun x ↦ ‖Q x‖ ^ 2) μ :=
    Integrable.of_bound (hmQ.norm.pow 2) (B ^ 2) (ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) hB).2 (hQB x))
  have hvariation : ∀ t : ℝ, ‖t‖ * L * ‖v‖ < 1 →
      μ.real univ ≤ ∫ x, ‖N x + t • Q x‖ ∂μ := by
    intro t ht
    obtain ⟨e, he⟩ := exists_rankOneVariation_homeomorph (lt_trans (by norm_num) hn) hL v t ht
    have hmF : MeasurableSet (rankOneVariation φ v t '' E) := by
      rw [← he]
      exact e.measurableEmbedding.measurableSet_image.mpr hmin.1
    have hs := symmDiff_image_rankOneVariation_subset E v t e he
    have hc : IsCompact (closure (symmDiff E (rankOneVariation φ v t '' E))) :=
      hcφ.of_isClosed_subset isClosed_closure hs
    have hlow := hmin.2.2 c R hR _ hmF hc (hs.trans hsφ)
    have hu := perimeter_image_rankOneVariation_le hn hmin Metric.isOpen_ball hP hφ hsφ hL v t ht
    have htoreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hlow.trans hu)
    rw [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)] at htoreal
    simpa only [μ, U, N, Q, Measure.real, Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball] using htoreal
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, ‖t‖ * L * ‖v‖ < 1 := by
    exact (show ContinuousAt (fun t : ℝ ↦ ‖t‖ * L * ‖v‖) 0 by fun_prop).eventually
      (gt_mem_nhds (by simp : ‖(0 : ℝ)‖ * L * ‖v‖ < 1))
  have hz : (∫ x, inner ℝ (N x) (Q x) ∂μ) = 0 := by
    apply linear_term_eq_zero_of_local_quadratic_nonneg _ ((∫ x, ‖Q x‖ ^ 2 ∂μ) / 2)
    filter_upwards [hevent] with t ht
    have hiA : Integrable (fun x ↦ ‖N x + t • Q x‖) μ := (hiN.add (hiQ.smul t)).norm
    have hiB : Integrable (fun x ↦ 1 + t * inner ℝ (N x) (Q x)) μ :=
      (integrable_const (1 : ℝ)).add (hiI.const_mul t)
    have hip : Integrable (fun x ↦ 1 + t * inner ℝ (N x) (Q x) +
        t ^ 2 / 2 * ‖Q x‖ ^ 2) μ := hiB.add (hiJ.const_mul (t ^ 2 / 2))
    have hupper := integral_mono_ae hiA hip (hNu.mono fun x hx ↦ norm_unit_add_smul_le_quadratic (N x) (Q x) hx t)
    rw [integral_add hiB (hiJ.const_mul _),
      integral_add (integrable_const (1 : ℝ)) (hiI.const_mul t), integral_const,
      integral_const_mul, integral_const_mul, smul_eq_mul, mul_one] at hupper
    have hlow := hvariation t ht
    nlinarith
  have hid : ∀ᵐ x ∂μ, inner ℝ (N x) (Q x) = inner ℝ (tangentialGradient E φ x) v := by
    filter_upwards [hNu] with x hx
    dsimp [N, Q, rankOneNormalError, tangentialGradient]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hx,
      one_pow, mul_one, inner_sub_left, real_inner_smul_left, inner_gradient_left]
    rw [real_inner_smul_right, real_inner_comm (approximateNormal E x) (gradient φ x)]
    ring
  exact (integral_congr_ae hid).symm.trans hz

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

def tangentialDivergence {n : ℕ} (E : Set (Euc n)) (V : Euc n → Euc n)
    (x : Euc n) : ℝ :=
  divergence V x - inner ℝ (approximateNormal E x)
    (fderiv ℝ V x (approximateNormal E x))

theorem tangentialDivergence_eq_sum {n : ℕ} (E : Set (Euc n))
    {V : Euc n → Euc n} (hV : Differentiable ℝ V) (x : Euc n) :
    tangentialDivergence E V x = ∑ i : Fin n,
      inner ℝ (tangentialGradient E
        (fun y ↦ inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i) (V y)) x)
        ((EuclideanSpace.basisFun (Fin n) ℝ) i) := by
  have hd (i : Fin n) : fderiv ℝ (fun y ↦ inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i) (V y)) x =
      (innerSL ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i)).comp (fderiv ℝ V x) :=
    ((innerSL ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i)).hasFDerivAt.comp x (hV x).hasFDerivAt).fderiv
  simp only [tangentialGradient, inner_sub_left, real_inner_smul_left,
    inner_gradient_left, Finset.sum_sub_distrib]
  change divergence V x - _ = (∑ i, fderiv ℝ (fun y ↦ inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i) (V y)) x ((EuclideanSpace.basisFun (Fin n) ℝ) i)) - _
  simp only [hd, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  congr 1
  conv_rhs => arg 2; ext i; rw [mul_comm]
  exact ((EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner _ _).symm

theorem tangentialDivergence_smul {n : ℕ} (E : Set (Euc n))
    {f : Euc n → ℝ} {V : Euc n → Euc n}
    (hf : Differentiable ℝ f) (hV : Differentiable ℝ V) (x : Euc n) :
    tangentialDivergence E (fun y ↦ f y • V y) x =
      f x * tangentialDivergence E V x +
        inner ℝ (tangentialGradient E f x) (V x) := by
  rw [tangentialDivergence, divergence_smul hf hV,
    fderiv_fun_smul (hf x) (hV x)]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, inner_add_right, real_inner_smul_right,
    tangentialDivergence, tangentialGradient, inner_sub_left, real_inner_smul_left,
    inner_gradient_left]
  ring

theorem tangentialDivergence_displacement {n : ℕ} (E : Set (Euc n))
    (a x : Euc n) (hN : ‖approximateNormal E x‖ = 1) (hn : 0 < n) :
    tangentialDivergence E (fun y ↦ y - a) x = (n - 1 : ℕ) := by
  have hd : fderiv ℝ (fun y : Euc n ↦ y - a) x = ContinuousLinearMap.id ℝ (Euc n) := by
    simpa only [id_eq] using ((hasFDerivAt_id x).sub_const a).fderiv
  simp only [tangentialDivergence, divergence, hd, ContinuousLinearMap.id_apply,
    real_inner_self_eq_norm_sq, hN, one_pow]
  simp only [(EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one, one_pow,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ n)).symm

def radialKernel {n : ℕ} (a : Euc n) (ε p : ℝ) (x : Euc n) : ℝ :=
  (‖x - a‖ ^ 2 + ε ^ 2) ^ (-p / 2)

theorem radialKernel_contDiff {n : ℕ} (a : Euc n) {ε : ℝ} (hε : 0 < ε) (p : ℝ) :
    ContDiff ℝ ∞ (radialKernel a ε p) := by
  apply (((show ContDiff ℝ ∞ (fun x : Euc n ↦ x - a) from contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)).add contDiff_const).rpow_const_of_ne
  intro x
  positivity

theorem radialKernel_hasFDerivAt {n : ℕ} (a x : Euc n) {ε : ℝ} (hε : 0 < ε) (p : ℝ) :
    HasFDerivAt (radialKernel a ε p)
      ((-p * (‖x - a‖ ^ 2 + ε ^ 2) ^ (-p / 2 - 1)) • innerSL ℝ (x - a)) x := by
  have hq := (((hasFDerivAt_id x).sub_const a).norm_sq).add_const (ε ^ 2)
  have hh := hq.rpow_const (p := -p / 2) (Or.inl (by positivity : ‖id x - a‖ ^ 2 + ε ^ 2 ≠ 0))
  have he : (-p / 2 * (‖x - a‖ ^ 2 + ε ^ 2) ^ (-p / 2 - 1)) * 2 =
      -p * (‖x - a‖ ^ 2 + ε ^ 2) ^ (-p / 2 - 1) := by ring
  have hmap : (-p / 2 * (‖id x - a‖ ^ 2 + ε ^ 2) ^ (-p / 2 - 1)) •
      (2 • (innerSL ℝ (id x - a)).comp (ContinuousLinearMap.id ℝ (Euc n))) =
      (-p * (‖x - a‖ ^ 2 + ε ^ 2) ^ (-p / 2 - 1)) • innerSL ℝ (x - a) := by
    ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, id_eq]
    ring
  rw [hmap] at hh
  exact hh

theorem tangentialDivergence_radial {n : ℕ} (E : Set (Euc n)) (hn : 0 < n)
    (a x : Euc n) {ε : ℝ} (hε : 0 < ε) (hN : ‖approximateNormal E x‖ = 1) :
    tangentialDivergence E (fun y ↦ radialKernel a ε (n - 1 : ℕ) y • (y - a)) x =
      (n - 1 : ℕ) * (‖x - a‖ ^ 2 + ε ^ 2) ^ (-((n - 1 : ℕ) : ℝ) / 2 - 1) *
        (ε ^ 2 + (inner ℝ (x - a) (approximateNormal E x)) ^ 2) := by
  rw [tangentialDivergence_smul E ((radialKernel_contDiff a hε _).differentiable (by simp))
    (show Differentiable ℝ (fun y : Euc n ↦ y - a) from differentiable_id.sub_const a), tangentialDivergence_displacement E a x hN hn]
  have hgrad : gradient (radialKernel a ε (n - 1 : ℕ)) x =
      (-((n - 1 : ℕ) : ℝ) * (‖x - a‖ ^ 2 + ε ^ 2) ^ (-((n - 1 : ℕ) : ℝ) / 2 - 1)) • (x - a) := by
    apply (InnerProductSpace.toDual ℝ (Euc n)).injective
    rw [toDual_gradient, (radialKernel_hasFDerivAt a x hε _).fderiv]
    simp only [map_smul]
    rfl
  rw [tangentialGradient, hgrad, inner_sub_left]
  simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, radialKernel]
  rw [real_inner_comm (approximateNormal E x) (x - a)]
  have hp : 0 < ‖x - a‖ ^ 2 + ε ^ 2 := by positivity
  have hr : (‖x - a‖ ^ 2 + ε ^ 2) ^ (-((n - 1 : ℕ) : ℝ) / 2) =
      (‖x - a‖ ^ 2 + ε ^ 2) ^ (-((n - 1 : ℕ) : ℝ) / 2 - 1) * (‖x - a‖ ^ 2 + ε ^ 2) := by
    calc
      _ = (‖x - a‖ ^ 2 + ε ^ 2) ^ ((-((n - 1 : ℕ) : ℝ) / 2 - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hp, Real.rpow_one]
  rw [hr]
  ring

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack
open RPI.Boundary

theorem tangentialGradient_integrable_ball_perimeter {n : ℕ}
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {R : ℝ} (hR : 0 < R) {φ : Euc n → ℝ}
    (hφ : ContDiff ℝ 1 φ) :
    Integrable (tangentialGradient E φ) ((perimeterMeasure E).restrict (Metric.ball c R)) := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c R)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c R hR⟩
  have hg : Continuous (gradient φ) := continuous_iff_continuousAt.mpr (fun x ↦
    continuousAt_gradient_of_contDiffAt hφ.contDiffAt)
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hg.continuousOn
  apply Integrable.of_bound (measurable_tangentialGradient hmin.1 hφ).aestronglyMeasurable (2 * M)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact (tangentialGradient_norm_le_twice E φ x).trans (by
    nlinarith [hM x (Metric.ball_subset_closedBall hx)])

theorem minimizing_tangentialDivergence_integral_eq_zero {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {R : ℝ} (hR : 0 < R) {V : Euc n → Euc n}
    (hV : ContDiff ℝ ∞ V) (hcV : HasCompactSupport V)
    (hsV : tsupport V ⊆ Metric.ball c R) :
    (∫ x in Metric.ball c R, tangentialDivergence E V x ∂perimeterMeasure E) = 0 := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let f : Fin n → Euc n → ℝ := fun i x ↦ inner ℝ (b i) (V x)
  have hf (i : Fin n) : ContDiff ℝ ∞ (f i) := contDiff_const.inner ℝ hV
  have hcf (i : Fin n) : HasCompactSupport (f i) :=
    hcV.comp_left (show inner ℝ (b i) (0 : Euc n) = 0 from inner_zero_right _)
  have hsf (i : Fin n) : tsupport (f i) ⊆ Metric.ball c R :=
    (tsupport_comp_subset (g := fun z : Euc n ↦ inner ℝ (b i) z)
      (inner_zero_right _) V).trans hsV
  have hz (i : Fin n) := minimizing_tangentialGradient_integral_eq_zero_local hn hmin c hR
    (hf i) (hcf i) (hsf i) (b i)
  have hi (i : Fin n) : Integrable (fun x ↦ inner ℝ (tangentialGradient E (f i) x) (b i))
      ((perimeterMeasure E).restrict (Metric.ball c R)) :=
    (tangentialGradient_integrable_ball_perimeter hmin c hR ((hf i).of_le (by simp))).inner_const (b i)
  simp_rw [tangentialDivergence_eq_sum E (hV.differentiable (by simp))]
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  exact Finset.sum_eq_zero fun i _ ↦ hz i

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
namespace RPIKernel

variable {X : Type*} [MetricSpace X]

theorem kernel_le_dyadic [MeasurableSpace X] [BorelSpace X]
    (a x : X) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (dist x a ^ (-s)) ≤ 1 + ∑' j : ℕ,
      (Metric.ball a (2 * (1 / 2 : ℝ) ^ j)).indicator
        (fun _ ↦ ENNReal.ofReal (((2 : ℝ) ^ s) ^ (j + 1))) x := by
  by_cases h0 : dist x a = 0
  · simp [h0, Real.zero_rpow (ne_of_lt (neg_neg_of_pos hs))]
  have hr : 0 < dist x a := lt_of_le_of_ne dist_nonneg (Ne.symm h0)
  by_cases hr1 : 1 ≤ dist x a
  · have hh : dist x a ^ (-s) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1) hr1 (by linarith : -s ≤ 0)
    exact (ENNReal.ofReal_le_one.mpr hh).trans (le_add_of_nonneg_right (by positivity))
  obtain ⟨j, hj₁, hj₂⟩ := exists_nat_pow_near_of_lt_one hr (le_of_not_ge hr1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hx : x ∈ Metric.ball a (2 * (1 / 2 : ℝ) ^ j) := by
    rw [Metric.mem_ball]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) j]
  have hb : dist x a ^ (-s) ≤ ((2 : ℝ) ^ s) ^ (j + 1) := by
    refine (Real.rpow_le_rpow_of_nonpos (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _) hj₁.le (by linarith)).trans_eq ?_
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_comm, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    rw [Real.rpow_neg_eq_inv_rpow]
    norm_num
  calc
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ s) ^ (j + 1)) := ENNReal.ofReal_le_ofReal hb
    _ = (Metric.ball a (2 * (1 / 2 : ℝ) ^ j)).indicator
        (fun _ ↦ ENNReal.ofReal (((2 : ℝ) ^ s) ^ (j + 1))) x := (indicator_of_mem hx (fun _ : X ↦ ENNReal.ofReal (((2 : ℝ) ^ s) ^ (j + 1)))).symm
    _ ≤ ∑' j : ℕ, (Metric.ball a (2 * (1 / 2 : ℝ) ^ j)).indicator
        (fun _ ↦ ENNReal.ofReal (((2 : ℝ) ^ s) ^ (j + 1))) x :=
      ENNReal.le_tsum (f := fun index : ℕ ↦
        (Metric.ball a (2 * (1 / 2 : ℝ) ^ index)).indicator
          (fun _ ↦ ENNReal.ofReal (((2 : ℝ) ^ s) ^ (index + 1))) x) j
    _ ≤ _ := le_add_of_nonneg_left (by positivity)

variable [MeasurableSpace X] [BorelSpace X]

theorem exists_kernel_integral_bound (μ : Measure X) [IsFiniteMeasure μ]
    {d s A : ℝ} (hs : 0 < s) (hsd : s < d) (hA : 0 ≤ A)
    (hg : ∀ (a : X) (r : ℝ), 0 < r → μ (Metric.ball a r) ≤ ENNReal.ofReal (A * r ^ d)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ a : X, ∫⁻ x, ENNReal.ofReal (dist x a ^ (-s)) ∂μ ≤ C := by
  let q : ℝ := (2 : ℝ) ^ s * (1 / 2 : ℝ) ^ d
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    have he : q = (2 : ℝ) ^ (s - d) := by
      dsimp [q]
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
        ← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1
    rw [he]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsd)
  let B : ℝ := A * (2 : ℝ) ^ d * (2 : ℝ) ^ s
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let C : ℝ≥0∞ := μ univ + ENNReal.ofReal B * ∑' j : ℕ, (ENNReal.ofReal q) ^ j
  have hqt : ∑' j : ℕ, (ENNReal.ofReal q) ^ j ≠ ⊤ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr (ENNReal.ofReal_lt_one.mpr hq1)).ne'
  refine ⟨C, ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqt⟩, ?_⟩
  intro a
  calc
    _ ≤ ∫⁻ x, 1 + ∑' j : ℕ, (Metric.ball a (2 * (1 / 2 : ℝ) ^ j)).indicator
        (fun _ ↦ ENNReal.ofReal (((2 : ℝ) ^ s) ^ (j + 1))) x ∂μ :=
      lintegral_mono fun x ↦ kernel_le_dyadic a x hs
    _ = μ univ + ∑' j : ℕ, ENNReal.ofReal (((2 : ℝ) ^ s) ^ (j + 1)) *
        μ (Metric.ball a (2 * (1 / 2 : ℝ) ^ j)) := by
      rw [lintegral_add_left measurable_const]
      rw [lintegral_tsum (fun j ↦ (measurable_const.indicator measurableSet_ball).aemeasurable)]
      simp only [lintegral_const, one_mul, lintegral_indicator measurableSet_ball,
        Measure.restrict_apply_univ]
    _ ≤ μ univ + ∑' j : ℕ, ENNReal.ofReal B * (ENNReal.ofReal q) ^ j := by
      apply add_le_add le_rfl
      apply ENNReal.tsum_le_tsum
      intro j
      calc
        _ ≤ ENNReal.ofReal (((2 : ℝ) ^ s) ^ (j + 1)) *
            ENNReal.ofReal (A * (2 * (1 / 2 : ℝ) ^ j) ^ d) :=
          by gcongr; exact hg a _ (by positivity)
        _ = ENNReal.ofReal B * (ENNReal.ofReal q) ^ j := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hq0,
            ← ENNReal.ofReal_mul hB]
          congr 1
          rw [Real.mul_rpow (by norm_num) (by positivity),
            ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
            mul_comm (j : ℝ) d, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2),
            pow_succ, mul_pow]
          dsimp [B, q]
          ring
    _ = C := by rw [ENNReal.tsum_mul_left]

end RPIKernel

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
namespace RPIKernel
open MeasureTheory
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem integrable_kernel_of_growth (μ : Measure X) [IsFiniteMeasure μ]
    {d s A : ℝ} (hs : 0 < s) (hsd : s < d) (hA : 0 ≤ A)
    (hg : ∀ (a : X) (r : ℝ), 0 < r → μ (Metric.ball a r) ≤ ENNReal.ofReal (A * r ^ d))
    (a : X) : Integrable (fun x ↦ dist x a ^ (-s)) μ := by
  obtain ⟨C, hC, hbound⟩ := exists_kernel_integral_bound μ hs hsd hA hg
  refine ⟨((continuous_id.dist (continuous_const (y := a))).measurable.pow_const _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all μ fun _ ↦ Real.rpow_nonneg dist_nonneg _)]
  exact (hbound a).trans_lt hC.lt_top

end RPIKernel

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
namespace RPISingularHarnack

theorem radialKernel_pos {n : ℕ} (a x : Euc n) {ε : ℝ} (hε : 0 < ε) (p : ℝ) :
    0 < radialKernel a ε p x := by
  apply Real.rpow_pos_of_pos
  positivity

theorem radialKernel_mul_dist_le {n : ℕ} (a x : Euc n) {ε p : ℝ}
    (hε : 0 < ε) (hp : 1 < p) :
    radialKernel a ε p x * ‖x - a‖ ≤ ‖x - a‖ ^ (-(p - 1)) := by
  by_cases h0 : ‖x - a‖ = 0
  · rw [h0, mul_zero]
    positivity
  have hr : 0 < ‖x - a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hpow := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hr)
    (le_add_of_nonneg_right (sq_pos_of_pos hε).le) (by linarith : -p / 2 ≤ 0)
  apply (mul_le_mul_of_nonneg_right hpow hr.le).trans_eq
  calc
    _ = ‖x - a‖ ^ ((2 : ℝ) * (-p / 2)) * ‖x - a‖ ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      congr 1
      simpa only [Nat.cast_ofNat] using (Real.rpow_natCast_mul hr.le 2 (-p / 2)).symm
    _ = ‖x - a‖ ^ ((2 : ℝ) * (-p / 2) + 1) := (Real.rpow_add hr _ _).symm
    _ = _ := by congr 1; ring

theorem radialKernel_mass_scaling {k ε : ℝ} (hε : 0 < ε) :
    ε ^ k * ε ^ 2 * (2 * ε ^ 2) ^ (-k / 2 - 1) = (2 : ℝ) ^ (-k / 2 - 1) := by
  rw [Real.mul_rpow (by norm_num) (sq_nonneg ε), ← Real.rpow_natCast_mul hε.le]
  norm_num only [Nat.cast_ofNat]
  rw [show ε ^ k * ε ^ 2 * ((2 : ℝ) ^ (-k / 2 - 1) * ε ^ ((2 : ℝ) * (-k / 2 - 1))) =
      (2 : ℝ) ^ (-k / 2 - 1) * (ε ^ k * ε ^ (2 : ℝ) * ε ^ ((2 : ℝ) * (-k / 2 - 1))) by
        rw [Real.rpow_two]; ring]
  rw [← Real.rpow_add hε, ← Real.rpow_add hε]
  ring_nf
  simp

end RPISingularHarnack

end

end OAI
