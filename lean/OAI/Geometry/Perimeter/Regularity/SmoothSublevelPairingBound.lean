import OAI.Geometry.Perimeter.Regularity.TangentialGradientComp

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack
open RPI

theorem smooth_sublevel_pairing_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A D : V) (a : ℝ) {ψ χ k : ℝ} (hk : 0 ≤ k) (hψ : 0 ≤ ψ)
    (hχ : χ ∈ Icc (0 : ℝ) 1) (hψχ : ψ ≤ k * χ) :
    inner ℝ A ((2 * a * ψ) • D - (a ^ 2 * χ) • A) ≤
      2 * k ^ 2 * ‖D‖ ^ 2 - (1 / 2 : ℝ) * (a ^ 2 * χ * ‖A‖ ^ 2) := by
  have hs0 : 0 ≤ Real.sqrt χ := Real.sqrt_nonneg _
  have hs2 : Real.sqrt χ ^ 2 = χ := Real.sq_sqrt hχ.1
  have hs1 : Real.sqrt χ ≤ 1 := by nlinarith [hχ.2]
  have hχs : χ ≤ Real.sqrt χ := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hψs : ψ ≤ k * Real.sqrt χ := hψχ.trans (mul_le_mul_of_nonneg_left hχs hk)
  have hi : a * inner ℝ A D ≤ |a| * (‖A‖ * ‖D‖) := by
    calc
      _ ≤ |a * inner ℝ A D| := le_abs_self _
      _ = |a| * |inner ℝ A D| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm A D) (abs_nonneg a)
  have hic := mul_le_mul_of_nonneg_left hi (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hψ)
  have hψb := mul_le_mul_of_nonneg_left hψs
    (show 0 ≤ 2 * |a| * ‖A‖ * ‖D‖ by positivity)
  have hY := sq_nonneg (|a| * Real.sqrt χ * ‖A‖ - 2 * k * ‖D‖)
  have hx : (|a| * Real.sqrt χ * ‖A‖) ^ 2 = a ^ 2 * χ * ‖A‖ ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs, hs2]
  rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  nlinarith [hx]

theorem sublevel_pairing_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A D : V) (a : ℝ) {ε k t : ℝ} (hε : 0 < ε) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    inner ℝ A ((2 * a * sublevelTest ε k t) • D -
      (a ^ 2 * sublevelSlope ε k t) • A) ≤
        2 * (if t < k then k ^ 2 * ‖D‖ ^ 2 else 0) -
          (1 / 2 : ℝ) * (a ^ 2 * sublevelSlope ε k t * ‖A‖ ^ 2) := by
  by_cases htk : t < k
  · simpa only [ite_eq_left htk, mul_assoc] using smooth_sublevel_pairing_bound A D a hk
      (sublevelTest_nonneg hε k t) (sublevelSlope_mem_Icc ε k t)
      (sublevelTest_controls hε hk ht)
  · simp [htk, sublevelTest_eq_zero hε (le_of_not_gt htk),
      sublevelSlope_eq_zero hε (le_of_not_gt htk)]

theorem wholeBoundary_sublevel_energy {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {h : Euc n → ℝ} {G : Euc n → Euc n}
    (hSob : WholeBoundarySobolev E h G) (hSuper : WholeBoundarySupersolution E G)
    (hh01 : ∀ᵐ x ∂boundaryArea E, 0 ≤ h x ∧ h x ≤ 1)
    {R : ℝ} (hR : 0 < R) {η : Euc n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ Metric.ball 0 R) {ε k : ℝ} (hε : 0 < ε) (hk : 0 ≤ k) :
    (∫ x in Metric.ball 0 R, η x ^ 2 * sublevelSlope ε k (h x) * ‖G x‖ ^ 2 ∂boundaryArea E) ≤
      4 * ∫ x in Metric.ball 0 R,
        (if h x < k then k ^ 2 * ‖tangentialGradient E η x‖ ^ 2 else 0) ∂boundaryArea E := by
  let μ := (boundaryArea E).restrict (Metric.ball 0 R)
  have : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using minimizing_boundaryArea_ball_lt_top hn hmin 0 hR⟩
  have hh := (hSob R hR).1
  have hG := (hSob R hR).2.1
  have hD := tangentialGradient_memLp_on_ball hn hmin hR (hη.of_le (by simp))
  let D := tangentialGradient E η
  let χ : Euc n → ℝ := fun x ↦ sublevelSlope ε k (h x)
  let ψ : Euc n → ℝ := fun x ↦ sublevelTest ε k (h x)
  have hχc : Continuous (sublevelSlope ε k) := by unfold sublevelSlope; fun_prop
  have hχm : AEStronglyMeasurable χ μ := hχc.comp_aestronglyMeasurable hh.aestronglyMeasurable
  have hψm : AEStronglyMeasurable ψ μ :=
    (sublevelTest_contDiff ε k).continuous.comp_aestronglyMeasurable hh.aestronglyMeasurable
  obtain ⟨M, hM⟩ := hcη.exists_bound_of_continuous hη.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (η 0)).trans (hM 0)
  have hψk : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ k := by
    filter_upwards [ae_restrict_of_ae hh01] with x hx
    rw [Real.norm_of_nonneg (sublevelTest_nonneg hε k (h x))]
    exact (sublevelTest_controls hε hk hx.1).trans
      (by nlinarith [(sublevelSlope_mem_Icc ε k (h x)).2])
  have hχb : ∀ x, ‖χ x‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_of_nonneg (sublevelSlope_mem_Icc ε k (h x)).1]
    exact (sublevelSlope_mem_Icc ε k (h x)).2
  have hc₁ : MemLp (fun x ↦ 2 * η x * ψ x) ∞ μ := by
    apply MemLp.of_bound ((aestronglyMeasurable_const.mul hη.continuous.aestronglyMeasurable).mul hψm)
      (2 * M * k)
    filter_upwards [hψk] with x hx
    simp only [Pi.mul_apply, norm_mul, Real.norm_ofNat]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hM x) (by norm_num)) hx (norm_nonneg _) (by positivity)
  have hc₂ : MemLp (fun x ↦ η x ^ 2 * χ x) ∞ μ := by
    apply MemLp.of_bound ((hη.continuous.aestronglyMeasurable.pow 2).mul hχm) (M ^ 2)
    exact ae_of_all _ fun x ↦ by
      simp only [Pi.mul_apply, Pi.pow_apply, norm_mul, norm_pow]
      exact (mul_le_mul ((sq_le_sq₀ (norm_nonneg _) hM0).2 (hM x)) (hχb x)
        (norm_nonneg _) (sq_nonneg M)).trans_eq (mul_one _)
  let B : Euc n → Euc n := fun x ↦ (2 * η x * ψ x) • D x - (η x ^ 2 * χ x) • G x
  have hB : MemLp B 2 μ := (hc₁.smul hD).sub (hc₂.smul hG)
  have hP : Integrable (fun x ↦ inner ℝ (G x) (B x)) μ := integrable_inner_of_memLp hG hB
  let J : Euc n → ℝ := fun x ↦ η x ^ 2 * χ x * ‖G x‖ ^ 2
  have hJm : AEStronglyMeasurable J μ :=
    ((hη.continuous.aestronglyMeasurable.pow 2).mul hχm).mul (hG.aestronglyMeasurable.norm.pow 2)
  have hGs := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hJ : Integrable J μ := (hGs.const_mul (M ^ 2)).mono' hJm (by
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (by dsimp [J]; positivity [(sublevelSlope_mem_Icc ε k (h x)).1])]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖G x‖)
    have hm : η x ^ 2 ≤ M ^ 2 := by simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg _) hM0).2 (hM x)
    exact (mul_le_mul hm (sublevelSlope_mem_Icc ε k (h x)).2
      (sublevelSlope_mem_Icc ε k (h x)).1 (sq_nonneg M)).trans_eq (mul_one _))
  let C : Euc n → ℝ := fun x ↦ if h x < k then k ^ 2 * ‖D x‖ ^ 2 else 0
  have hDs := (memLp_two_iff_integrable_sq_norm hD.aestronglyMeasurable).mp hD
  have hCm : AEStronglyMeasurable C μ := by
    exact ((hD.aestronglyMeasurable.norm.pow 2).const_mul (k ^ 2)).indicator₀
      (hh.aestronglyMeasurable.nullMeasurableSet_lt aestronglyMeasurable_const)
  have hC : Integrable C μ := (hDs.const_mul (k ^ 2)).mono' hCm (by
    filter_upwards [] with x
    change ‖if h x < k then k ^ 2 * ‖D x‖ ^ 2 else 0‖ ≤ _
    split_ifs
    · rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg k) (sq_nonneg ‖D x‖))]
    · simp only [norm_zero]
      positivity)
  have htest := wholeBoundarySupersolution_nonlinear_test hn hmin hSob hSuper hh01
    hR hη hcη hsη (sublevelTest_contDiff ε k) (sublevelTest_nonneg hε k)
    (sublevelTest_lipschitz ε k) (show (0 : ℝ) ≤ 1 by norm_num) (fun t ↦ by
      rw [(sublevelTest_hasDerivAt ε k t).deriv, norm_neg,
        Real.norm_of_nonneg (sublevelSlope_mem_Icc ε k t).1]
      exact (sublevelSlope_mem_Icc ε k t).2)
  have htest' : 0 ≤ ∫ x, inner ℝ (G x) (B x) ∂μ := by
    convert htest using 1
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by
      dsimp only
      rw [(sublevelTest_hasDerivAt ε k (h x)).deriv]
      simp only [B, D, ψ, χ, mul_neg, neg_smul, sub_eq_add_neg]
  have hi := integral_mono_ae hP ((hC.const_mul 2).sub (hJ.const_mul (1 / 2))) (by
    filter_upwards [ae_restrict_of_ae hh01] with x hx
    exact sublevel_pairing_bound (G x) (D x) (η x) hε hk hx.1)
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (hC.const_mul 2) (hJ.const_mul (1 / 2)), integral_const_mul,
    integral_const_mul] at hi
  change (∫ x, J x ∂μ) ≤ 4 * ∫ x, C x ∂μ
  linarith

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

def rankOneVariation {n : ℕ} (φ : Euc n → ℝ) (v : Euc n) (t : ℝ) (x : Euc n) : Euc n :=
  x + (t * φ x) • v

def rankOneJacobian {n : ℕ} (φ : Euc n → ℝ) (v : Euc n) (t : ℝ) (x : Euc n) : ℝ :=
  1 + t * fderiv ℝ φ x v

def rankOnePiola {n : ℕ} (φ : Euc n → ℝ) (v : Euc n) (t : ℝ)
    (W : Euc n → Euc n) (x : Euc n) : Euc n :=
  rankOneJacobian φ v t x • W (rankOneVariation φ v t x) -
    (t * fderiv ℝ φ x (W (rankOneVariation φ v t x))) • v

theorem rankOneVariation_contDiff {n : ℕ} {φ : Euc n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (v : Euc n) (t : ℝ) :
    ContDiff ℝ ∞ (rankOneVariation φ v t) :=
  contDiff_id.add ((contDiff_const.mul hφ).smul contDiff_const)

theorem rankOneVariation_hasFDerivAt {n : ℕ} {φ : Euc n → ℝ} {x : Euc n}
    (hφ : DifferentiableAt ℝ φ x) (v : Euc n) (t : ℝ) :
    HasFDerivAt (rankOneVariation φ v t)
      (ContinuousLinearMap.id ℝ (Euc n) + (t • fderiv ℝ φ x).smulRight v) x := by
  convert (hasFDerivAt_id x).add ((hφ.hasFDerivAt.const_mul t).smul_const v) using 1
  rfl

theorem divergence_comp_rankOneVariation {n : ℕ} {φ : Euc n → ℝ}
    {W : Euc n → Euc n} (hφ : Differentiable ℝ φ) (hW : Differentiable ℝ W)
    (v : Euc n) (t : ℝ) (x : Euc n) :
    divergence (W ∘ rankOneVariation φ v t) x =
      divergence W (rankOneVariation φ v t x) +
        t * fderiv ℝ φ x (fderiv ℝ W (rankOneVariation φ v t x) v) := by
  rw [divergence]
  rw [((hW _).hasFDerivAt.comp x (rankOneVariation_hasFDerivAt (hφ x) v t)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, smul_eq_mul, map_add, map_smul,
    inner_add_right, real_inner_smul_right, Finset.sum_add_distrib]
  change divergence W (rankOneVariation φ v t x) + _ = _
  congr 1
  simp_rw [← inner_gradient_left, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  exact (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner _ _

theorem rankOneJacobian_hasFDerivAt {n : ℕ} {φ : Euc n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (v : Euc n) (t : ℝ) (x : Euc n) :
    HasFDerivAt (rankOneJacobian φ v t)
      (t • (ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ φ) x)) x := by
  have hd : Differentiable ℝ (fderiv ℝ φ) := (hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  convert (((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x
    (hd x).hasFDerivAt).const_mul t).const_add 1 using 1
  rfl

theorem rankOneJacobian_contDiff {n : ℕ} {φ : Euc n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (v : Euc n) (t : ℝ) :
    ContDiff ℝ ∞ (rankOneJacobian φ v t) :=
  contDiff_const.add (contDiff_const.mul ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const))

theorem rankOnePiola_contDiff {n : ℕ} {φ : Euc n → ℝ} {W : Euc n → Euc n}
    (hφ : ContDiff ℝ ∞ φ) (hW : ContDiff ℝ ∞ W) (v : Euc n) (t : ℝ) :
    ContDiff ℝ ∞ (rankOnePiola φ v t W) := by
  have hF := hW.comp (rankOneVariation_contDiff hφ v t)
  exact ((rankOneJacobian_contDiff hφ v t).smul hF).sub
    ((contDiff_const.mul ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply hF)).smul contDiff_const)

theorem divergence_rankOnePiola {n : ℕ} {φ : Euc n → ℝ} {W : Euc n → Euc n}
    (hφ : ContDiff ℝ ∞ φ) (hW : ContDiff ℝ ∞ W) (v : Euc n) (t : ℝ) (x : Euc n) :
    divergence (rankOnePiola φ v t W) x =
      rankOneJacobian φ v t x * divergence W (rankOneVariation φ v t x) := by
  let F := rankOneVariation φ v t
  let A := fderiv ℝ W (F x)
  let L := fderiv ℝ φ x
  let H := fderiv ℝ (fderiv ℝ φ) x
  have hdφ : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hdW : Differentiable ℝ W := hW.differentiable (by simp)
  have hdL : Differentiable ℝ (fderiv ℝ φ) := (hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hdF : Differentiable ℝ F := (rankOneVariation_contDiff hφ v t).differentiable (by simp)
  have hdV : Differentiable ℝ (W ∘ F) := hdW.comp hdF
  have hdJ := (rankOneJacobian_contDiff hφ v t).differentiable (by simp)
  have hdw : Differentiable ℝ (fun y ↦ t * fderiv ℝ φ y (W (F y))) :=
    (hdL.clm_apply hdV).const_mul t
  change divergence ((fun y ↦ rankOneJacobian φ v t y • W (F y)) -
    (fun y ↦ (t * fderiv ℝ φ y (W (F y))) • v)) x = _
  have hd1 : Differentiable ℝ (fun y ↦ rankOneJacobian φ v t y • W (F y)) :=
    hdJ.fun_smul hdV
  have hd2 : Differentiable ℝ (fun y ↦ (t * fderiv ℝ φ y (W (F y))) • v) :=
    hdw.smul_const v
  rw [divergence_sub hd1 hd2, Pi.sub_apply]
  have hds := divergence_smul hdJ hdV x
  dsimp only [Function.comp_apply] at hds
  rw [hds, divergence_smul hdw (differentiable_const v)]
  have hconst : divergence (fun _ : Euc n ↦ v) x = 0 := by simp [divergence]
  rw [hconst, mul_zero, zero_add]
  rw [inner_gradient_left, inner_gradient_left]
  rw [(rankOneJacobian_hasFDerivAt hφ v t x).fderiv]
  have hcomp := (hdW (F x)).hasFDerivAt.comp x (rankOneVariation_hasFDerivAt (hdφ x) v t)
  have happ := (hdL x).hasFDerivAt.clm_apply hcomp
  have happ' := (happ.const_mul t).fderiv
  dsimp only [Function.comp_apply] at happ'
  rw [happ']
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.flip_apply, smul_eq_mul, add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply]
  have hsym : H (W (F x)) v = H v (W (F x)) :=
    second_derivative_symmetric (fun y ↦ (hdφ y).hasFDerivAt) (hdL x).hasFDerivAt _ _
  have hdiv := divergence_comp_rankOneVariation hdφ hdW v t x
  change _ = _ at hdiv
  change rankOneJacobian φ v t x * divergence (W ∘ F) x + t * H (W (F x)) v -
    t * (L (A (v + (t * L v) • v)) + H v (W (F x))) = _
  rw [hdiv, hsym]
  simp only [F, rankOneJacobian, map_add, map_smul, smul_eq_mul, A, L]
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

theorem det_id_add_smulRight {n : ℕ} (L : Euc n →L[ℝ] ℝ) (v : Euc n) :
    (ContinuousLinearMap.id ℝ (Euc n) + L.smulRight v).det = 1 + L v := by
  classical
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  change LinearMap.det (LinearMap.id + L.toLinearMap.smulRight v) = _
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_id,
    LinearMap.toMatrix_smulRight]
  have hm : Matrix.vecMulVec (b.repr v) (L.toLinearMap ∘ b) =
      Matrix.replicateCol Unit (b.repr v) * Matrix.replicateRow Unit (L.toLinearMap ∘ b) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  rw [hm, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  have hb := b.sum_repr v
  apply_fun L at hb
  change (∑ i, L (b i) * b.repr v i) = L v
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using hb

theorem det_fderiv_rankOneVariation {n : ℕ} {φ : Euc n → ℝ}
    (hφ : Differentiable ℝ φ) (v : Euc n) (t : ℝ) (x : Euc n) :
    (fderiv ℝ (rankOneVariation φ v t) x).det = rankOneJacobian φ v t x := by
  rw [(rankOneVariation_hasFDerivAt (hφ x) v t).fderiv, det_id_add_smulRight]
  rfl

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

theorem exists_rankOneVariation_homeomorph {n : ℕ} (hn : 0 < n)
    {φ : Euc n → ℝ} {L : ℝ≥0} (hL : LipschitzWith L φ)
    (v : Euc n) (t : ℝ) (ht : ‖t‖ * L * ‖v‖ < 1) :
    ∃ e : Euc n ≃ₜ Euc n, (e : Euc n → Euc n) = rankOneVariation φ v t := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let c : ℝ≥0 := ‖t‖₊ * L * ‖v‖₊
  have ha : ApproximatesLinearOn (rankOneVariation φ v t)
      ((ContinuousLinearEquiv.refl ℝ (Euc n)) : Euc n →L[ℝ] Euc n) univ c := by
    intro x _ y _
    have heq : rankOneVariation φ v t x - rankOneVariation φ v t y - (x - y) =
        (t * (φ x - φ y)) • v := by
      unfold rankOneVariation
      rw [mul_sub, sub_smul]
      abel
    change ‖rankOneVariation φ v t x - rankOneVariation φ v t y - (x - y)‖ ≤ _
    rw [heq, norm_smul, norm_mul]
    have hb := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hL.norm_sub_le x y) (norm_nonneg t)) (norm_nonneg v)
    simpa only [c, NNReal.coe_mul, coe_nnnorm, mul_assoc, mul_left_comm, mul_comm] using hb
  have hc : c < ‖((ContinuousLinearEquiv.refl ℝ (Euc n)).symm : Euc n →L[ℝ] Euc n)‖₊⁻¹ := by
    simpa [c, ← NNReal.coe_lt_coe] using ht
  exact ⟨ha.toHomeomorph _ (Or.inr hc), rfl⟩

theorem rankOneJacobian_pos {n : ℕ} {φ : Euc n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (v : Euc n) (t : ℝ)
    (ht : ‖t‖ * L * ‖v‖ < 1) (x : Euc n) : 0 < rankOneJacobian φ v t x := by
  have hnorm : ‖t * fderiv ℝ φ x v‖ ≤ ‖t‖ * L * ‖v‖ := by
    rw [norm_mul]
    calc
      _ ≤ ‖t‖ * (‖fderiv ℝ φ x‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((fderiv ℝ φ x).le_opNorm v) (norm_nonneg t)
      _ ≤ ‖t‖ * (L * ‖v‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg v)) (norm_nonneg t)
      _ = _ := by ring
  have hb := (neg_abs_le (t * fderiv ℝ φ x v))
  simp only [Real.norm_eq_abs] at hnorm ht
  unfold rankOneJacobian
  linarith

theorem rankOneVariation_eq_self_of_notMem_tsupport {n : ℕ}
    (φ : Euc n → ℝ) (v : Euc n) (t : ℝ) {x : Euc n} (hx : x ∉ tsupport φ) :
    rankOneVariation φ v t x = x := by
  simp [rankOneVariation, image_eq_zero_of_notMem_tsupport hx]

theorem Homeomorph.image_eq_of_eqOn_compl {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ X) (U : Set X) (heq : ∀ x ∉ U, e x = x) : e '' U = U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_contra hx
    have hh := e.injective (heq (e y) hx)
    exact hx (hh.symm ▸ hy)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    by_contra hn
    have hh := heq (e.symm x) hn
    rw [e.apply_symm_apply] at hh
    exact hn (hh ▸ hx)

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

theorem rankOnePiola_tsupport_subset {n : ℕ} {φ : Euc n → ℝ} {W : Euc n → Euc n}
    (hφ : ContDiff ℝ ∞ φ) (v : Euc n) (t : ℝ) :
    tsupport (rankOnePiola φ v t W) ⊆ (rankOneVariation φ v t) ⁻¹' tsupport W := by
  apply closure_minimal _ ((isClosed_tsupport W).preimage (rankOneVariation_contDiff hφ v t).continuous)
  intro x hx
  by_contra hn
  have hw : W (rankOneVariation φ v t x) = 0 := image_eq_zero_of_notMem_tsupport hn
  exact hx (by simp [rankOnePiola, hw])

theorem rankOnePiola_hasCompactSupport {n : ℕ} {φ : Euc n → ℝ} {W : Euc n → Euc n}
    (hφ : ContDiff ℝ ∞ φ) (v : Euc n) (t : ℝ) (e : Euc n ≃ₜ Euc n)
    (he : (e : Euc n → Euc n) = rankOneVariation φ v t) (hW : HasCompactSupport W) :
    HasCompactSupport (rankOnePiola φ v t W) := by
  have hc : IsCompact ((rankOneVariation φ v t) ⁻¹' tsupport W) := by
    rw [← he, ← e.image_symm]
    exact hW.image e.symm.continuous
  exact hc.of_isClosed_subset (isClosed_tsupport _) (rankOnePiola_tsupport_subset hφ v t)

theorem rankOnePiola_tsupport_subset_region {n : ℕ} {φ : Euc n → ℝ} {W : Euc n → Euc n}
    {U : Set (Euc n)} (hφ : ContDiff ℝ ∞ φ) (v : Euc n) (t : ℝ)
    (e : Euc n ≃ₜ Euc n) (he : (e : Euc n → Euc n) = rankOneVariation φ v t)
    (hφU : tsupport φ ⊆ U) (hWU : tsupport W ⊆ U) :
    tsupport (rankOnePiola φ v t W) ⊆ U := by
  intro x hx
  by_contra hnx
  have hf : e x = x := by
    rw [he]
    exact rankOneVariation_eq_self_of_notMem_tsupport φ v t (fun h ↦ hnx (hφU h))
  have hW := rankOnePiola_tsupport_subset hφ v t hx
  change rankOneVariation φ v t x ∈ tsupport W at hW
  rw [← he, hf] at hW
  exact hnx (hWU hW)

theorem rankOneVariation_image_region {n : ℕ} {φ : Euc n → ℝ} {U : Set (Euc n)}
    (v : Euc n) (t : ℝ) (e : Euc n ≃ₜ Euc n)
    (he : (e : Euc n → Euc n) = rankOneVariation φ v t) (hφU : tsupport φ ⊆ U) :
    rankOneVariation φ v t '' U = U := by
  rw [← he]
  apply Homeomorph.image_eq_of_eqOn_compl
  intro x hx
  rw [he]
  exact rankOneVariation_eq_self_of_notMem_tsupport φ v t (fun h ↦ hx (hφU h))

theorem symmDiff_image_rankOneVariation_subset {n : ℕ} {φ : Euc n → ℝ}
    (E : Set (Euc n)) (v : Euc n) (t : ℝ) (e : Euc n ≃ₜ Euc n)
    (he : (e : Euc n → Euc n) = rankOneVariation φ v t) :
    closure (symmDiff E (rankOneVariation φ v t '' E)) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hnx
  have hfix : e x = x := by rw [he]; exact rankOneVariation_eq_self_of_notMem_tsupport φ v t hnx
  have himem : x ∈ rankOneVariation φ v t '' E ↔ x ∈ E := by
    rw [← he]
    constructor
    · rintro ⟨y, hy, hye⟩
      exact (e.injective (hye.trans hfix.symm)) ▸ hy
    · intro h
      exact ⟨x, h, hfix⟩
  exact (mem_symmDiff.mp hx).elim (fun h ↦ h.2 (himem.mpr h.1)) (fun h ↦ h.2 (himem.mp h.1))

end RPISingularHarnack

end

end OAI
