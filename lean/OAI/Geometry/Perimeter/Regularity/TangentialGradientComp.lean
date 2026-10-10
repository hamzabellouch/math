import OAI.Geometry.Perimeter.Regularity.ExistsLocalPolarEqApproximateNormal

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack
open RPI RPI.Boundary

theorem tangentialGradient_comp {n : ℕ} (E : Set (Euc n))
    {f : Euc n → ℝ} {T : ℝ → ℝ} {x : Euc n}
    (hf : DifferentiableAt ℝ f x) (hT : DifferentiableAt ℝ T (f x)) :
    tangentialGradient E (T ∘ f) x = deriv T (f x) • tangentialGradient E f x := by
  have hgrad : gradient (T ∘ f) x = deriv T (f x) • gradient f x := by
    apply (InnerProductSpace.toDual ℝ (Euc n)).injective
    simp only [map_smul, toDual_gradient]
    exact (hT.hasDerivAt.comp_hasFDerivAt x hf.hasFDerivAt).fderiv
  simp only [tangentialGradient, hgrad, real_inner_smul_left]
  module

theorem tangentialGradient_nonlinear_test {n : ℕ} (E : Set (Euc n))
    {η f : Euc n → ℝ} {ψ : ℝ → ℝ} {x : Euc n}
    (hη : DifferentiableAt ℝ η x) (hf : DifferentiableAt ℝ f x)
    (hψ : DifferentiableAt ℝ ψ (f x)) :
    tangentialGradient E (fun y ↦ (η y * η y) * ψ (f y)) x =
      (2 * η x * ψ (f x)) • tangentialGradient E η x +
      (η x ^ 2 * deriv ψ (f x)) • tangentialGradient E f x := by
  have hprod := tangentialGradient_mul E (hη.mul hη) (hψ.comp x hf)
  simp only [Pi.mul_apply, Function.comp_apply] at hprod
  rw [hprod]
  change (η x * η x) • tangentialGradient E (ψ ∘ f) x +
    ψ (f x) • tangentialGradient E (fun y ↦ η y * η y) x = _
  rw [tangentialGradient_mul E hη hη]
  rw [tangentialGradient_comp E hf hψ]
  module

theorem wholeBoundarySupersolution_nonlinear_test {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {h : Euc n → ℝ} {G : Euc n → Euc n}
    (hSob : WholeBoundarySobolev E h G) (hSuper : WholeBoundarySupersolution E G)
    (hh01 : ∀ᵐ x ∂boundaryArea E, 0 ≤ h x ∧ h x ≤ 1)
    {R : ℝ} (hR : 0 < R) {η : Euc n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ Metric.ball 0 R)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψpos : ∀ t, 0 ≤ ψ t)
    {K : ℝ≥0} (hψLip : LipschitzWith K ψ)
    {L : ℝ} (hL : 0 ≤ L) (hdψ : ∀ t, ‖deriv ψ t‖ ≤ L) :
    0 ≤ ∫ x in Metric.ball 0 R, inner ℝ (G x)
      ((2 * η x * ψ (h x)) • tangentialGradient E η x +
        (η x ^ 2 * deriv ψ (h x)) • G x) ∂boundaryArea E := by
  let μ := (boundaryArea E).restrict (Metric.ball 0 R)
  have : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using minimizing_boundaryArea_ball_lt_top hn hmin 0 hR⟩
  obtain ⟨hh, hG, u, hu, huh, huG⟩ := hSob R hR
  have hu0 : Tendsto (fun j ↦ vectorEnergy μ (fun x ↦ u j x - h x)) atTop (𝓝 0) := by
    simpa only [vectorEnergy, Real.norm_eq_abs] using huh
  have hum : ∀ j, AEStronglyMeasurable (u j) μ :=
    fun j ↦ (hu j).1.continuous.aestronglyMeasurable
  obtain ⟨σ, hσ, hpoint⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (tendsto_eLpNorm_two_of_vectorEnergy_zero_of_aestronglyMeasurable
      (fun j ↦ (hum j).sub hh.aestronglyMeasurable) hu0)).exists_seq_tendsto_ae
  let F : ℕ → Euc n → Euc n := fun j ↦ tangentialGradient E (u (σ j))
  let D := tangentialGradient E η
  have hF : ∀ j, MemLp (F j) 2 μ := fun j ↦
    tangentialGradient_memLp_on_ball hn hmin hR ((hu (σ j)).1.of_le (by simp))
  have hD : MemLp D 2 μ := tangentialGradient_memLp_on_ball hn hmin hR (hη.of_le (by simp))
  have hdcont : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  obtain ⟨M₀, hM₀⟩ := hcη.exists_bound_of_continuous hη.continuous
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hηM : ∀ᵐ x ∂μ, ‖η x‖ ≤ M := ae_of_all _ fun x ↦ (hM₀ x).trans (le_max_left _ _)
  have hgradη : Continuous (gradient η) := continuous_iff_continuousAt.mpr (fun x ↦
    continuousAt_gradient_of_contDiffAt (hη.of_le (by simp)).contDiffAt)
  obtain ⟨N₀, hN₀⟩ := (isCompact_closedBall (0 : Euc n) R).exists_bound_of_continuousOn hgradη.continuousOn
  let N := 2 * max N₀ 0
  have hN : 0 ≤ N := by positivity
  have hDN : ∀ᵐ x ∂μ, ‖D x‖ ≤ N := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (tangentialGradient_norm_le_twice E η x).trans (by
      dsimp [N]; nlinarith [hN₀ x (Metric.ball_subset_closedBall hx), le_max_left N₀ 0])
  let B : Euc n → Euc n := fun x ↦
    (2 * η x * ψ (h x)) • D x + (η x ^ 2 * deriv ψ (h x)) • G x
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hψ.continuous.continuousOn
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hψC : ∀ᵐ x ∂μ, ‖ψ (h x)‖ ≤ C := by
    filter_upwards [ae_restrict_of_ae hh01] with x hx
    exact (hC₀ (h x) hx).trans (le_max_left _ _)
  have hca : MemLp (fun x ↦ 2 * η x * ψ (h x)) ∞ μ := by
    apply MemLp.of_bound ((aestronglyMeasurable_const.mul hη.continuous.aestronglyMeasurable).mul
      (hψ.continuous.comp_aestronglyMeasurable hh.aestronglyMeasurable)) (2 * M * C)
    filter_upwards [hηM, hψC] with x hx hy
    simpa only [Pi.mul_apply, norm_mul, Real.norm_ofNat] using mul_le_mul
      (mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 2)) hy (norm_nonneg _) (by positivity)
  have hcb : MemLp (fun x ↦ η x ^ 2 * deriv ψ (h x)) ∞ μ := by
    apply MemLp.of_bound ((hη.continuous.aestronglyMeasurable.pow 2).mul
      (hdcont.comp_aestronglyMeasurable hh.aestronglyMeasurable)) (M ^ 2 * L)
    filter_upwards [hηM] with x hx
    rw [Pi.mul_apply, Pi.pow_apply, norm_mul, norm_pow]
    exact mul_le_mul ((sq_le_sq₀ (norm_nonneg _) hM).mpr hx) (hdψ _) (norm_nonneg _) (sq_nonneg _)
  have hB : MemLp B 2 μ := (hca.smul hD).add (hcb.smul hG)
  let ξ : ℕ → Euc n → ℝ := fun j x ↦ (η x * η x) * ψ (u (σ j) x)
  have hξ : ∀ j, ContDiff ℝ ∞ (ξ j) := fun j ↦ (hη.mul hη).mul (hψ.comp (hu (σ j)).1)
  have hξc : ∀ j, HasCompactSupport (ξ j) := fun _ ↦ hcη.mul_right.mul_right
  have hξgrad : ∀ j x, tangentialGradient E (ξ j) x =
      (2 * η x * ψ (u (σ j) x)) • D x + (η x ^ 2 * deriv ψ (u (σ j) x)) • F j x := by
    intro j x
    exact tangentialGradient_nonlinear_test E (hη.differentiable (by simp) x)
      ((hu (σ j)).1.differentiable (by simp) x) (hψ.differentiable (by simp) _)
  have henergy : Tendsto (fun j ↦ vectorEnergy μ
      (fun x ↦ tangentialGradient E (ξ j) x - B x)) atTop (𝓝 0) := by
    simp_rw [hξgrad]
    exact vectorEnergy_nonlinear_test_tendsto (fun j ↦ hum (σ j)) hh.aestronglyMeasurable
      hη.continuous.aestronglyMeasurable hD.aestronglyMeasurable hF hG hM hN hηM hDN
      (hu0.comp hσ.tendsto_atTop) (huG.comp hσ.tendsto_atTop) hpoint hψLip
      (deriv ψ) hdcont hL hdψ
  have hξLp : ∀ j, MemLp (tangentialGradient E (ξ j)) 2 μ := fun j ↦
    tangentialGradient_memLp_on_ball hn hmin hR ((hξ j).of_le (by simp))
  have hlim0 := tendsto_integral_inner_of_L2_zero hG
    (fun j x ↦ tangentialGradient E (ξ j) x - B x) (fun j ↦ (hξLp j).sub hB)
    (tendsto_eLpNorm_two_toReal_of_vectorEnergy_zero_of_aestronglyMeasurable
      (fun j ↦ ((hξLp j).sub hB).aestronglyMeasurable) henergy)
  have hlim : Tendsto (fun j ↦ ∫ x, inner ℝ (G x) (tangentialGradient E (ξ j) x) ∂μ)
      atTop (𝓝 (∫ x, inner ℝ (G x) (B x) ∂μ)) := by
    have hj : ∀ j, (∫ x, inner ℝ (G x) (tangentialGradient E (ξ j) x - B x) ∂μ) =
        (∫ x, inner ℝ (G x) (tangentialGradient E (ξ j) x) ∂μ) -
        ∫ x, inner ℝ (G x) (B x) ∂μ := fun j ↦ by
      simp_rw [inner_sub_right]
      exact integral_sub (integrable_inner_of_memLp hG (hξLp j)) (integrable_inner_of_memLp hG hB)
    change Tendsto (fun j ↦ ∫ x, inner ℝ (G x) (tangentialGradient E (ξ j) x - B x) ∂μ) atTop (𝓝 0) at hlim0
    simp_rw [hj] at hlim0
    simpa only [sub_add_cancel, zero_add] using hlim0.add_const (∫ x, inner ℝ (G x) (B x) ∂μ)
  apply ge_of_tendsto hlim
  exact Filter.Eventually.of_forall fun j ↦ by
    change 0 ≤ ∫ x in Metric.ball 0 R, inner ℝ (G x) (tangentialGradient E (ξ j) x) ∂boundaryArea E
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hSuper (ξ j) (hξ j) (hξc j) (fun x ↦ mul_nonneg (mul_self_nonneg _) (hψpos _))
    · intro x hx
      rw [tangentialGradient_eq_zero_of_notMem_tsupport E
        (fun hx' ↦ hx (hsη (tsupport_mul_subset_left (tsupport_mul_subset_left hx')))), inner_zero_right]

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
open RPI

theorem logTest_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith ⟨2 / ε ^ 2, by positivity⟩ (logTest ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le ((logTest_contDiff hε).differentiable (by simp))
  intro t
  change ‖deriv (logTest ε) t‖ ≤ 2 / ε ^ 2
  rw [(logTest_hasDerivAt hε t).deriv]
  exact logSlope_bound hε t

def logRootWeight (ε t : ℝ) : ℝ := Real.sqrt (-logSlope ε t)
def logTestRatio (ε t : ℝ) : ℝ := logTest ε t / logRootWeight ε t

theorem logRootWeight_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 < logRootWeight ε t := Real.sqrt_pos.2 (neg_pos.mpr (logSlope_neg hε t))

theorem logRootWeight_sq {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    logRootWeight ε t ^ 2 = -logSlope ε t :=
  Real.sq_sqrt (neg_nonneg.mpr (logSlope_neg hε t).le)

theorem logTestRatio_mem_Icc {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    logTestRatio ε t ∈ Icc (0 : ℝ) 1 := by
  have hw := logRootWeight_pos hε t
  have hψ := logTest_pos hε t
  refine ⟨(div_pos hψ hw).le, (div_le_one hw).2 ?_⟩
  nlinarith [logRootWeight_sq hε t, logTest_sq_le_neg_slope hε ht]

theorem logRootWeight_bound {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    logRootWeight ε t ≤ Real.sqrt (2 / ε ^ 2) := by
  apply Real.sqrt_le_sqrt
  have hh := logSlope_bound hε t
  rwa [Real.norm_eq_abs, abs_of_neg (logSlope_neg hε t)] at hh

theorem logTestRatio_continuous {ε : ℝ} (hε : 0 < ε) : Continuous (logTestRatio ε) := by
  exact (logTest_contDiff hε).continuous.div
    (Real.continuous_sqrt.comp (logSlope_continuous hε).neg)
    (fun t ↦ (logRootWeight_pos hε t).ne')

theorem logTest_pairing {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ε : ℝ} (hε : 0 < ε) (t a : ℝ) (G D : V) :
    inner ℝ ((a * logRootWeight ε t) • G)
      ((2 * logTestRatio ε t) • D - (a * logRootWeight ε t) • G) =
      inner ℝ G ((2 * a * logTest ε t) • D + (a ^ 2 * logSlope ε t) • G) := by
  simp only [inner_sub_right, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  have heq : logRootWeight ε t * logTestRatio ε t = logTest ε t := by
    dsimp [logTestRatio]
    exact mul_div_cancel₀ _ (logRootWeight_pos hε t).ne'
  calc
    _ = 2 * a * (logRootWeight ε t * logTestRatio ε t) * inner ℝ G D -
        a ^ 2 * logRootWeight ε t ^ 2 * inner ℝ G G := by ring
    _ = _ := by rw [heq, logRootWeight_sq hε]; ring

theorem log_weight_le_energy {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) (a : ℝ) (G : V) :
    a ^ 2 * ‖G‖ ^ 2 / (t + ε) ^ 2 ≤ 2 * ‖(a * logRootWeight ε t) • G‖ ^ 2 := by
  have hh := mul_le_mul_of_nonneg_left (logSlope_controls_log_weight hε ht)
    (mul_nonneg (sq_nonneg a) (sq_nonneg ‖G‖))
  rw [norm_smul, norm_mul, mul_pow, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.norm_eq_abs, sq_abs, logRootWeight_sq hε]
  simpa only [div_eq_mul_inv, mul_one, mul_assoc, mul_left_comm, mul_comm] using hh

theorem wholeBoundary_log_caccioppoli {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {h : Euc n → ℝ} {G : Euc n → Euc n}
    (hSob : WholeBoundarySobolev E h G) (hSuper : WholeBoundarySupersolution E G)
    (hh01 : ∀ᵐ x ∂boundaryArea E, 0 ≤ h x ∧ h x ≤ 1)
    {R : ℝ} (hR : 0 < R) {η : Euc n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ Metric.ball 0 R) {ε : ℝ} (hε : 0 < ε) :
    (∫ x in Metric.ball 0 R, η x ^ 2 * ‖G x‖ ^ 2 / (h x + ε) ^ 2 ∂boundaryArea E) ≤
      8 * ∫ x in Metric.ball 0 R, ‖tangentialGradient E η x‖ ^ 2 ∂boundaryArea E := by
  let μ := (boundaryArea E).restrict (Metric.ball 0 R)
  have hh := (hSob R hR).1
  have hG := (hSob R hR).2.1
  have hD := tangentialGradient_memLp_on_ball hn hmin hR (hη.of_le (by simp))
  let A : Euc n → Euc n := fun x ↦ (η x * logRootWeight ε (h x)) • G x
  have hwc : Continuous (logRootWeight ε) := Real.continuous_sqrt.comp (logSlope_continuous hε).neg
  have hAm : AEStronglyMeasurable A μ :=
    (hη.continuous.aestronglyMeasurable.mul
      (hwc.comp_aestronglyMeasurable hh.aestronglyMeasurable)).smul hG.aestronglyMeasurable
  obtain ⟨M, hM⟩ := hcη.exists_bound_of_continuous hη.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (η 0)).trans (hM 0)
  have hA : MemLp A 2 μ := by
    apply hG.of_le_mul (c := M * Real.sqrt (2 / ε ^ 2)) hAm
    exact ae_of_all _ fun x ↦ by
      change ‖(η x * logRootWeight ε (h x)) • G x‖ ≤ _
      rw [norm_smul, norm_mul, Real.norm_of_nonneg (logRootWeight_pos hε _).le]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hM x) (logRootWeight_bound hε _)
        (logRootWeight_pos hε _).le hM0) (norm_nonneg _)
  have htest0 := wholeBoundarySupersolution_nonlinear_test hn hmin hSob hSuper hh01
    hR hη hcη hsη (logTest_contDiff hε) (fun t ↦ (logTest_pos hε t).le)
    (logTest_lipschitz hε) (show 0 ≤ 2 / ε ^ 2 by positivity)
    (fun t ↦ by rw [(logTest_hasDerivAt hε t).deriv]; exact logSlope_bound hε t)
  have htest : 0 ≤ ∫ x, inner ℝ (A x)
      ((2 * (1 - (1 - logTestRatio ε (h x)))) • tangentialGradient E η x - A x) ∂μ := by
    have heq : (fun x ↦ inner ℝ (A x)
        ((2 * (1 - (1 - logTestRatio ε (h x)))) • tangentialGradient E η x - A x)) =
        fun x ↦ inner ℝ (G x)
          ((2 * η x * logTest ε (h x)) • tangentialGradient E η x +
            (η x ^ 2 * deriv (logTest ε) (h x)) • G x) := by
      funext x
      rw [(logTest_hasDerivAt hε (h x)).deriv]
      simp only [sub_sub_cancel]
      exact logTest_pairing hε (h x) (η x) (G x) (tangentialGradient E η x)
    rwa [heq]
  have hbound := truncation_test_energy hA hD
    (aestronglyMeasurable_const.sub
      ((logTestRatio_continuous hε).comp_aestronglyMeasurable hh.aestronglyMeasurable))
    (show ∀ᵐ x ∂μ, (1 - logTestRatio ε (h x)) ∈ Icc (0 : ℝ) 1 from by
      filter_upwards [ae_restrict_of_ae hh01] with x hx
      have hb := logTestRatio_mem_Icc hε hx.1
      constructor <;> linarith [hb.1, hb.2]) htest
  have hAs : Integrable (fun x ↦ ‖A x‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hAm).mp hA
  let W : Euc n → ℝ := fun x ↦ η x ^ 2 * ‖G x‖ ^ 2 / (h x + ε) ^ 2
  have hWm : AEStronglyMeasurable W μ :=
    (((hη.continuous.aemeasurable.pow_const 2).mul
      (hG.aestronglyMeasurable.norm.pow 2).aemeasurable).div
      ((hh.aestronglyMeasurable.add_const ε).pow 2).aemeasurable).aestronglyMeasurable
  have hWle : ∀ᵐ x ∂μ, W x ≤ 2 * ‖A x‖ ^ 2 := by
    filter_upwards [ae_restrict_of_ae hh01] with x hx
    exact log_weight_le_energy hε hx.1 (η x) (G x)
  have hW : Integrable W μ := (hAs.const_mul 2).mono' hWm (by
    filter_upwards [hWle] with x hx
    rw [Real.norm_of_nonneg (by dsimp [W]; positivity)]
    exact hx)
  have hi := integral_mono_ae hW (hAs.const_mul 2) hWle
  rw [integral_const_mul] at hi
  change (∫ x, W x ∂μ) ≤ 8 * ∫ x, ‖tangentialGradient E η x‖ ^ 2 ∂μ
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

def smoothPositive (ε s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, Real.smoothTransition (t / ε)

theorem smoothPositive_hasDerivAt (ε s : ℝ) :
    HasDerivAt (smoothPositive ε) (Real.smoothTransition (s / ε)) s := by
  have hc : Continuous (fun t : ℝ ↦ Real.smoothTransition (t / ε)) := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

@[simp] theorem smoothPositive_deriv (ε s : ℝ) :
    deriv (smoothPositive ε) s = Real.smoothTransition (s / ε) :=
  (smoothPositive_hasDerivAt ε s).deriv

theorem smoothPositive_contDiff (ε : ℝ) : ContDiff ℝ ∞ (smoothPositive ε) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s ↦ (smoothPositive_hasDerivAt ε s).differentiableAt, ?_⟩
  simp only [funext (smoothPositive_deriv ε)]
  fun_prop

theorem smoothPositive_of_nonpos {ε s : ℝ} (hε : 0 < ε) (hs : s ≤ 0) :
    smoothPositive ε s = 0 := by
  unfold smoothPositive
  calc
    _ = ∫ _t in (0 : ℝ)..s, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hs] at ht
      exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht.2 hε.le)
    _ = 0 := by simp

theorem smoothPositive_nonneg {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 ≤ smoothPositive ε s := by
  by_cases hs : 0 ≤ s
  · exact intervalIntegral.integral_nonneg hs (fun t _ ↦ Real.smoothTransition.nonneg _)
  · rw [smoothPositive_of_nonpos hε (le_of_not_ge hs)]

theorem smoothPositive_le_mul {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) :
    smoothPositive ε s ≤ s * Real.smoothTransition (s / ε) := by
  have hc : Continuous (fun t : ℝ ↦ Real.smoothTransition (t / ε)) := by fun_prop
  have hh := intervalIntegral.integral_mono_on hs (hc.intervalIntegrable 0 s)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ Real.smoothTransition (s / ε)) volume 0 s)
    (fun t ht ↦ Real.smoothTransition.monotone (div_le_div_of_nonneg_right ht.2 hε.le))
  simpa only [smoothPositive, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hh

theorem smoothPositive_le_self {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) :
    smoothPositive ε s ≤ s := by
  exact (smoothPositive_le_mul hε hs).trans (by nlinarith [Real.smoothTransition.le_one (s / ε)])

theorem sub_parameter_le_smoothPositive {ε s : ℝ} (hε : 0 < ε) :
    s - ε ≤ smoothPositive ε s := by
  by_cases hs : s ≤ ε
  · exact (sub_nonpos.mpr hs).trans (smoothPositive_nonneg hε s)
  · have hes : ε ≤ s := le_of_not_ge hs
    have hc : Continuous (fun t : ℝ ↦ Real.smoothTransition (t / ε)) := by fun_prop
    unfold smoothPositive
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 ε)
      (hc.intervalIntegrable ε s)]
    have heq : (∫ t in ε..s, Real.smoothTransition (t / ε)) = s - ε := by
      calc
        _ = ∫ _t in ε..s, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hes] at ht
          exact Real.smoothTransition.one_of_one_le ((le_div_iff₀ hε).2 (by simpa using ht.1))
        _ = _ := by simp
    rw [heq]
    have hp := intervalIntegral.integral_nonneg (μ := volume) hε.le
      (fun t (_ : t ∈ Icc (0 : ℝ) ε) ↦ Real.smoothTransition.nonneg (t / ε))
    linarith

def sublevelTest (ε k t : ℝ) : ℝ := smoothPositive ε (k - t)
def sublevelSlope (ε k t : ℝ) : ℝ := Real.smoothTransition ((k - t) / ε)

theorem sublevelTest_contDiff (ε k : ℝ) : ContDiff ℝ ∞ (sublevelTest ε k) :=
  (smoothPositive_contDiff ε).comp (contDiff_const.sub contDiff_id)

theorem sublevelTest_hasDerivAt (ε k t : ℝ) :
    HasDerivAt (sublevelTest ε k) (-sublevelSlope ε k t) t := by
  convert (smoothPositive_hasDerivAt ε (k - t)).comp t ((hasDerivAt_id t).const_sub k) using 1 <;>
    (first | rfl | simp [sublevelSlope])

theorem sublevelTest_nonneg {ε : ℝ} (hε : 0 < ε) (k t : ℝ) :
    0 ≤ sublevelTest ε k t := smoothPositive_nonneg hε _

theorem sublevelSlope_mem_Icc (ε k t : ℝ) : sublevelSlope ε k t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem sublevelTest_controls {ε k t : ℝ} (hε : 0 < ε) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    sublevelTest ε k t ≤ k * sublevelSlope ε k t := by
  by_cases htk : t ≤ k
  · exact (smoothPositive_le_mul hε (sub_nonneg.mpr htk)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (sublevelSlope_mem_Icc ε k t).1)
  · rw [sublevelTest, smoothPositive_of_nonpos hε (by linarith)]
    exact mul_nonneg hk (sublevelSlope_mem_Icc ε k t).1

theorem sublevelTest_eq_zero {ε k t : ℝ} (hε : 0 < ε) (ht : k ≤ t) :
    sublevelTest ε k t = 0 := smoothPositive_of_nonpos hε (sub_nonpos.mpr ht)

theorem sublevelSlope_eq_zero {ε k t : ℝ} (hε : 0 < ε) (ht : k ≤ t) :
    sublevelSlope ε k t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hε.le)

theorem sublevelTest_lipschitz (ε k : ℝ) : LipschitzWith 1 (sublevelTest ε k) := by
  apply lipschitzWith_of_nnnorm_deriv_le ((sublevelTest_contDiff ε k).differentiable (by simp))
  intro t
  change ‖deriv (sublevelTest ε k) t‖ ≤ 1
  rw [(sublevelTest_hasDerivAt ε k t).deriv, norm_neg,
    Real.norm_of_nonneg (sublevelSlope_mem_Icc ε k t).1]
  exact (sublevelSlope_mem_Icc ε k t).2

end RPISingularHarnack

end

end OAI
