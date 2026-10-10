import OAI.Geometry.Perimeter.Regularity.ExistsTangentialGradientBallBound

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
namespace RPIKernel
variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]

lemma tendsto_lintegral_norm_of_L2 [NormedSpace ℝ V] (μ : Measure X) [IsFiniteMeasure μ]
    {F : ℕ → X → V} {G : X → V} (hF : ∀ j, MemLp (F j) 2 μ) (hG : MemLp G 2 μ)
    (hlim : Tendsto (fun j ↦ eLpNorm (fun x ↦ F j x - G x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫⁻ x, ENNReal.ofReal ‖F j x‖ ∂μ) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal ‖G x‖ ∂μ)) := by
  have hfinite : μ univ ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ)
  have ht : Tendsto (fun j ↦ eLpNorm (fun x ↦ F j x - G x) 2 μ * μ univ ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hlim (Or.inr hfinite)
  have hnorm : Tendsto (fun j ↦ eLpNorm (fun x ↦ ‖F j x‖ - ‖G x‖) 1 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ ↦ bot_le)
    intro j
    calc
      _ ≤ eLpNorm (fun x ↦ F j x - G x) 1 μ := eLpNorm_mono_ae
        ((hF j).aestronglyMeasurable.norm.sub hG.aestronglyMeasurable.norm)
        (ae_of_all _ fun x ↦ by simpa only [Pi.sub_apply, Real.norm_eq_abs] using abs_norm_sub_norm_le (F j x) (G x))
      _ ≤ _ := by
        simpa only [Pi.sub_apply, ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one,
          show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := fun x ↦ F j x - G x) (by norm_num : (1 : ℝ≥0∞) ≤ 2) ((hF j).aestronglyMeasurable.sub hG.aestronglyMeasurable)
  have hiF (j : ℕ) : Integrable (F j) μ := memLp_one_iff_integrable.mp ((hF j).mono_exponent (by norm_num))
  have hiG : Integrable G μ := memLp_one_iff_integrable.mp (hG.mono_exponent (by norm_num))
  have hI := tendsto_integral_of_L1' (fun x ↦ ‖G x‖)
    (Eventually.of_forall fun j ↦ (hiF j).norm) hnorm
  have H := ENNReal.continuous_ofReal.tendsto (∫ x, ‖G x‖ ∂μ) |>.comp hI
  change Tendsto (fun j ↦ ENNReal.ofReal (∫ x, ‖F j x‖ ∂μ)) atTop
    (𝓝 (ENNReal.ofReal (∫ x, ‖G x‖ ∂μ))) at H
  simp_rw [ofReal_integral_norm_eq_lintegral_enorm (hiF _),
    ofReal_integral_norm_eq_lintegral_enorm hiG] at H
  simpa only [ofReal_norm] using H

variable [NormedSpace ℝ V]

theorem sobolev_limit (μ : Measure X) [IsFiniteMeasure μ]
    {f : ℕ → X → ℝ} {h : X → ℝ} {F : ℕ → X → V} {G : X → V}
    (hf : ∀ j, AEMeasurable (f j) μ)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun j ↦ f j x) atTop (𝓝 (h x)))
    (hF : ∀ j, MemLp (F j) 2 μ) (hG : MemLp G 2 μ)
    (hlim : Tendsto (fun j ↦ eLpNorm (fun x ↦ F j x - G x) 2 μ) atTop (𝓝 0))
    {p : ℝ} {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ j, (∫⁻ x, ENNReal.ofReal (f j x) ^ p ∂μ) ≤
      C * (∫⁻ x, ENNReal.ofReal ‖F j x‖ ∂μ) ^ p) :
    (∫⁻ x, ENNReal.ofReal (h x) ^ p ∂μ) ≤ C * (∫⁻ x, ENNReal.ofReal ‖G x‖ ∂μ) ^ p := by
  have hI := tendsto_lintegral_norm_of_L2 μ hF hG hlim
  have hpow := (ENNReal.continuous_rpow_const (y := p)).tendsto (∫⁻ x, ENNReal.ofReal ‖G x‖ ∂μ) |>.comp hI
  have hR := ENNReal.Tendsto.const_mul hpow (Or.inr hC)
  calc
    _ = ∫⁻ x, liminf (fun j ↦ ENNReal.ofReal (f j x) ^ p) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hpoint] with x hx
      exact (((ENNReal.continuous_rpow_const (y := p)).comp ENNReal.continuous_ofReal).tendsto (h x) |>.comp hx).liminf_eq.symm
    _ ≤ liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (f j x) ^ p ∂μ) atTop :=
      lintegral_liminf_le' (fun j ↦ ((hf j).ennreal_ofReal).pow_const p)
    _ ≤ liminf (fun j ↦ C * (∫⁻ x, ENNReal.ofReal ‖F j x‖ ∂μ) ^ p) atTop :=
      liminf_le_liminf (Eventually.of_forall hbound)
    _ = _ := hR.liminf_eq

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
open RPI RPI.Boundary

theorem wholeBoundary_nonlinear_approximation {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {h : Euc n → ℝ} {G : Euc n → Euc n}
    (hSob : WholeBoundarySobolev E h G)
    (hh01 : ∀ᵐ x ∂boundaryArea E, 0 ≤ h x ∧ h x ≤ 1)
    {R : ℝ} (hR : 0 < R) {η : Euc n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ Metric.ball 0 R)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψpos : ∀ t, 0 ≤ ψ t)
    {K : ℝ≥0} (hψLip : LipschitzWith K ψ)
    {L : ℝ} (hL : 0 ≤ L) (hdψ : ∀ t, ‖deriv ψ t‖ ≤ L) :
    let μ := (boundaryArea E).restrict (Metric.ball 0 R)
    let B := fun x ↦ (2 * η x * ψ (h x)) • tangentialGradient E η x +
      (η x ^ 2 * deriv ψ (h x)) • G x
    MemLp B 2 μ ∧ ∃ ξ : ℕ → Euc n → ℝ,
      (∀ j, ContDiff ℝ ∞ (ξ j) ∧ HasCompactSupport (ξ j) ∧
        tsupport (ξ j) ⊆ Metric.ball 0 R ∧ ∀ x, 0 ≤ ξ j x) ∧
      (∀ᵐ x ∂μ, Tendsto (fun j ↦ ξ j x) atTop (𝓝 (η x ^ 2 * ψ (h x)))) ∧
      Tendsto (fun j ↦ vectorEnergy μ (fun x ↦ tangentialGradient E (ξ j) x - B x)) atTop (𝓝 0) := by
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
      (fun index ↦ (hum index).sub hh.aestronglyMeasurable) hu0)).exists_seq_tendsto_ae
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
  refine ⟨hB, ξ, ?_, ?_, henergy⟩
  · intro j
    refine ⟨hξ j, hξc j, ?_, fun x ↦ mul_nonneg (mul_self_nonneg _) (hψpos _)⟩
    exact (tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans hsη
  · filter_upwards [hpoint] with x hx
    simpa only [ξ, ← sq] using
      (tendsto_const_nhds.mul ((hψ.continuous.tendsto (h x)).comp hx) :
        Tendsto (fun j ↦ (η x * η x) * ψ (u (σ j) x)) atTop (𝓝 ((η x * η x) * ψ (h x))))

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
namespace RPISingularHarnack
open RPI

theorem wholeBoundary_sublevel_sobolev {n : ℕ} (hn : 2 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {h : Euc n → ℝ} {G : Euc n → Euc n}
    (hSob : WholeBoundarySobolev E h G)
    (hh01 : ∀ᵐ x ∂boundaryArea E, 0 ≤ h x ∧ h x ≤ 1)
    {R p : ℝ} (hR : 0 < R) (hp : 1 < p)
    (hpk : (((n - 1 : ℕ) : ℝ) - 1) * p < (n - 1 : ℕ)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ η : Euc n → ℝ,
      ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Metric.ball 0 R →
      ∀ ε k : ℝ, 0 < ε → 0 ≤ k →
      (∫⁻ x in Metric.ball 0 R, ENNReal.ofReal (η x ^ 2 * sublevelTest ε k (h x)) ^ p ∂boundaryArea E) ≤
        C * (∫⁻ x in Metric.ball 0 R, ENNReal.ofReal
          ‖(2 * η x * sublevelTest ε k (h x)) • tangentialGradient E η x -
            (η x ^ 2 * sublevelSlope ε k (h x)) • G x‖ ∂boundaryArea E) ^ p := by
  obtain ⟨C, hC, hb⟩ := minimizing_boundaryArea_sobolev hn hmin 0 hR hp hpk
  refine ⟨C, hC, ?_⟩
  intro η hη hcη hsη ε k hε hk
  let μ := (boundaryArea E).restrict (Metric.ball 0 R)
  let : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using minimizing_boundaryArea_ball_lt_top (by omega : 1 < n) hmin 0 hR⟩
  obtain ⟨hB, ξ, hξ, hpoint, henergy⟩ := wholeBoundary_nonlinear_approximation (by omega : 1 < n)
    hmin hSob hh01 hR hη hcη hsη (sublevelTest_contDiff ε k) (sublevelTest_nonneg hε k)
    (sublevelTest_lipschitz ε k) (show (0 : ℝ) ≤ 1 by norm_num) (fun t ↦ by
      rw [(sublevelTest_hasDerivAt ε k t).deriv, norm_neg,
        Real.norm_of_nonneg (sublevelSlope_mem_Icc ε k t).1]
      exact (sublevelSlope_mem_Icc ε k t).2)
  have hF : ∀ j, MemLp (tangentialGradient E (ξ j)) 2 μ := fun j ↦
    tangentialGradient_memLp_on_ball (by omega : 1 < n) hmin hR ((hξ j).1.of_le (by simp))
  have H := RPIKernel.sobolev_limit μ (fun j ↦ (hξ j).1.continuous.measurable.aemeasurable)
    hpoint hF hB (tendsto_eLpNorm_two_of_vectorEnergy_zero_of_aestronglyMeasurable
      (fun index ↦ (hF index).aestronglyMeasurable.sub hB.aestronglyMeasurable) henergy) hC
    (fun j ↦ hb (ξ j) (hξ j).1 (hξ j).2.1 (hξ j).2.2.1 (hξ j).2.2.2)
  simpa only [(sublevelTest_hasDerivAt ε k _).deriv, mul_neg, neg_smul, sub_eq_add_neg] using H

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
open scoped ENNReal Topology ContDiff
namespace RPIKernel
open Classical

lemma weighted_sublevel_gradient_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G D : V) {a ψ χ k N : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hχ : χ ∈ Icc (0 : ℝ) 1) (hψ : 0 ≤ ψ) (hψk : ψ ≤ k * χ)
    (hk : 0 < k) (hN : 0 < N) (hD : ‖D‖ ≤ N) :
    ‖(2 * a * ψ) • D - (a ^ 2 * χ) • G‖ ≤
      (5 / 2 : ℝ) * (k * N) + (a ^ 2 * χ * ‖G‖ ^ 2) / (2 * (k * N)) := by
  have ha0 := ha.1
  have ha1 := ha.2
  have hχ0 := hχ.1
  have hχ1 := hχ.2
  have hχa : 0 ≤ a ^ 2 * χ := by positivity
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
  have hχa1 : a ^ 2 * χ ≤ 1 := by nlinarith [hχ.1, hχ.2, sq_nonneg a]
  have hL : 0 < k * N := mul_pos hk hN
  have hψbound : ψ ≤ k := by nlinarith [hχ.2]
  have hfirst : ‖(2 * a * ψ) • D‖ ≤ 2 * (k * N) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (2 * 1 * k) * N := by gcongr
      _ = _ := by ring
  have hsecond : ‖(a ^ 2 * χ) • G‖ ≤ (1 / 2 : ℝ) * (k * N) +
      (a ^ 2 * χ * ‖G‖ ^ 2) / (2 * (k * N)) := by
    rw [norm_smul, Real.norm_of_nonneg hχa]
    have hh : (a ^ 2 * χ * ‖G‖) ^ 2 ≤ a ^ 2 * χ * ‖G‖ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hχa1) (mul_nonneg hχa (sq_nonneg ‖G‖))]
    have H : a ^ 2 * χ * ‖G‖ * (2 * (k * N)) ≤ (k * N) ^ 2 + a ^ 2 * χ * ‖G‖ ^ 2 := by
      nlinarith [sq_nonneg (a ^ 2 * χ * ‖G‖ - k * N)]
    have HD := (le_div_iff₀ (by positivity : 0 < 2 * (k * N))).mpr H
    calc
      _ ≤ ((k * N) ^ 2 + a ^ 2 * χ * ‖G‖ ^ 2) / (2 * (k * N)) := HD
      _ = _ := by field_simp
  exact (norm_sub_le _ _).trans (by linarith)

lemma integral_norm_sublevel_bound {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure X) [IsFiniteMeasure μ] {A : Set X} (hA : NullMeasurableSet A μ)
    {B : X → V} {J : X → ℝ} (hB : Integrable B μ) (hJ : Integrable J μ)
    {L : ℝ} (hL : 0 < L)
    (hpoint : ∀ᵐ x ∂μ, ‖B x‖ ≤ (if x ∈ A then (5 / 2 : ℝ) * L else 0) + J x / (2 * L))
    (henergy : (∫ x, J x ∂μ) ≤ 4 * L ^ 2 * μ.real A) :
    (∫ x, ‖B x‖ ∂μ) ≤ 5 * L * μ.real A := by
  classical
  have hiA : Integrable (fun x ↦ if x ∈ A then (5 / 2 : ℝ) * L else 0) μ :=
    (integrable_const ((5 / 2 : ℝ) * L)).indicator₀ hA
  have hmono := integral_mono_ae hB.norm (hiA.add (hJ.div_const _)) hpoint
  have hIA : (∫ x, (if x ∈ A then (5 / 2 : ℝ) * L else 0) ∂μ) = (5 / 2 : ℝ) * L * μ.real A := by
    change (∫ x, A.indicator (fun _ ↦ (5 / 2 : ℝ) * L) x ∂μ) = _
    rw [integral_indicator₀ hA]
    simp only [setIntegral_const, smul_eq_mul]
    ring
  simp only [Pi.add_apply] at hmono
  rw [integral_add hiA (hJ.div_const _), hIA, integral_div] at hmono
  have he := div_le_div_of_nonneg_right henergy (by positivity : 0 ≤ 2 * L)
  have hc : 4 * L ^ 2 * μ.real A / (2 * L) = 2 * L * μ.real A := by field_simp; ring
  rw [hc] at he
  nlinarith [(measureReal_nonneg : 0 ≤ μ.real A)]

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
open scoped ENNReal Topology ContDiff
namespace RPISingularHarnack
open RPI RPI.Boundary Classical

theorem wholeBoundary_sublevel_L1 {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {h : Euc n → ℝ} {G : Euc n → Euc n}
    (hSob : WholeBoundarySobolev E h G) (hSuper : WholeBoundarySupersolution E G)
    (hh01 : ∀ᵐ x ∂boundaryArea E, 0 ≤ h x ∧ h x ≤ 1)
    {R r ε k N : ℝ} (hR : 0 < R) (hrR : r ≤ R) (hε : 0 < ε) (hk : 0 < k) (hN : 0 < N)
    {η : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ Metric.ball 0 r) (hη01 : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    (hD : ∀ x, ‖tangentialGradient E η x‖ ≤ N) :
    (∫⁻ x in Metric.ball 0 R, ENNReal.ofReal
      ‖(2 * η x * sublevelTest ε k (h x)) • tangentialGradient E η x -
        (η x ^ 2 * sublevelSlope ε k (h x)) • G x‖ ∂boundaryArea E) ≤
      ENNReal.ofReal (5 * k * N) * boundaryArea E (Metric.ball 0 r ∩ {x | h x < k}) := by
  classical
  let μ := (boundaryArea E).restrict (Metric.ball 0 R)
  let : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using minimizing_boundaryArea_ball_lt_top hn hmin 0 hR⟩
  have hsR := hsη.trans (Metric.ball_subset_ball hrR)
  have hh := (hSob R hR).1
  have hG := (hSob R hR).2.1
  let A := Metric.ball (0 : Euc n) r ∩ {x | h x < k}
  have hAm : NullMeasurableSet A μ := measurableSet_ball.nullMeasurableSet.inter
    (nullMeasurableSet_lt hh.aestronglyMeasurable.aemeasurable aemeasurable_const)
  let J := fun x ↦ η x ^ 2 * sublevelSlope ε k (h x) * ‖G x‖ ^ 2
  let B := fun x ↦ (2 * η x * sublevelTest ε k (h x)) • tangentialGradient E η x -
    (η x ^ 2 * sublevelSlope ε k (h x)) • G x
  have hχc : Continuous (sublevelSlope ε k) := by unfold sublevelSlope; fun_prop
  have hJm : AEStronglyMeasurable J μ :=
    ((hη.continuous.aestronglyMeasurable.pow 2).mul (hχc.comp_aestronglyMeasurable hh.aestronglyMeasurable)).mul (hG.aestronglyMeasurable.norm.pow 2)
  have hJ : Integrable J μ := ((memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG).mono' hJm (by
    filter_upwards [] with x
    have ha0 := (hη01 x).1
    have ha1 := (hη01 x).2
    have hc0 := (sublevelSlope_mem_Icc ε k (h x)).1
    have hc1 := (sublevelSlope_mem_Icc ε k (h x)).2
    rw [Real.norm_of_nonneg (by dsimp [J]; positivity)]
    have hb : η x ^ 2 * sublevelSlope ε k (h x) ≤ 1 := by nlinarith [sq_nonneg (η x)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (sq_nonneg ‖G x‖))
  have hBA : MemLp B 2 μ := by
    have H := (wholeBoundary_nonlinear_approximation hn hmin hSob hh01 hR hη hcη hsR
      (sublevelTest_contDiff ε k) (sublevelTest_nonneg hε k) (sublevelTest_lipschitz ε k)
      (show (0 : ℝ) ≤ 1 by norm_num) (fun t ↦ by
        rw [(sublevelTest_hasDerivAt ε k t).deriv, norm_neg,
          Real.norm_of_nonneg (sublevelSlope_mem_Icc ε k t).1]
        exact (sublevelSlope_mem_Icc ε k t).2)).1
    simpa only [B, μ, (sublevelTest_hasDerivAt ε k _).deriv, mul_neg, neg_smul, sub_eq_add_neg] using H
  have hB : Integrable B μ := memLp_one_iff_integrable.mp (hBA.mono_exponent (by norm_num))
  have hz {x : Euc n} (hx : x ∉ Metric.ball 0 r) : η x = 0 ∧ tangentialGradient E η x = 0 := by
    have ht : x ∉ tsupport η := fun ht ↦ hx (hsη ht)
    exact ⟨image_eq_zero_of_notMem_tsupport ht, tangentialGradient_eq_zero_of_notMem_tsupport E ht⟩
  have hpoint : ∀ᵐ x ∂μ, ‖B x‖ ≤ (if x ∈ A then (5 / 2 : ℝ) * (k * N) else 0) + J x / (2 * (k * N)) := by
    filter_upwards [ae_restrict_of_ae hh01] with x hx
    by_cases hxr : x ∈ Metric.ball 0 r
    · by_cases hxk : h x < k
      · simp only [A, mem_inter_iff, mem_ofPred_eq, hxr, hxk, and_self, ite_true]
        exact RPIKernel.weighted_sublevel_gradient_bound (G x) (tangentialGradient E η x)
          (hη01 x) (sublevelSlope_mem_Icc ε k (h x)) (sublevelTest_nonneg hε k (h x))
          (sublevelTest_controls hε hk.le hx.1) hk hN (hD x)
      · simp [B, J, A, hxk, sublevelTest_eq_zero hε (le_of_not_gt hxk),
          sublevelSlope_eq_zero hε (le_of_not_gt hxk)]
    · obtain ⟨hηx, hDx⟩ := hz hxr
      simp [B, J, A, hxr, hηx, hDx]
  have hi : Integrable (fun x ↦ if h x < k then k ^ 2 * ‖tangentialGradient E η x‖ ^ 2 else 0) μ := by
    have hm : NullMeasurableSet {x | h x < k} μ := nullMeasurableSet_lt hh.aestronglyMeasurable.aemeasurable aemeasurable_const
    exact ((memLp_two_iff_integrable_sq_norm
      (tangentialGradient_memLp_on_ball hn hmin hR (hη.of_le (by simp))).aestronglyMeasurable).mp
      (tangentialGradient_memLp_on_ball hn hmin hR (hη.of_le (by simp)))).const_mul (k ^ 2) |>.indicator₀ hm
  have hconst : Integrable (A.indicator (fun _ ↦ (k * N) ^ 2)) μ := (integrable_const _).indicator₀ hAm
  have hcost : (∫ x, (if h x < k then k ^ 2 * ‖tangentialGradient E η x‖ ^ 2 else 0) ∂μ) ≤
      (k * N) ^ 2 * μ.real A := by
    calc
      _ ≤ ∫ x, A.indicator (fun _ ↦ (k * N) ^ 2) x ∂μ := by
        apply integral_mono_ae hi hconst
        exact ae_of_all _ fun x ↦ by
          by_cases hxr : x ∈ Metric.ball 0 r
          · by_cases hxk : h x < k
            · simp only [A, mem_inter_iff, mem_ofPred_eq, hxr, hxk, and_self, ite_true, indicator_of_mem]
              nlinarith [sq_le_sq₀ (norm_nonneg (tangentialGradient E η x)) hN.le |>.mpr (hD x)]
            · simp [A, hxk]
          · simp [A, hxr, (hz hxr).2]
      _ = _ := by rw [integral_indicator₀ hAm, setIntegral_const]; simp [Measure.real, smul_eq_mul, mul_comm]
  have henergy := wholeBoundary_sublevel_energy hn hmin hSob hSuper hh01 hR hη hcη hsR hε hk.le
  have hreal := RPIKernel.integral_norm_sublevel_bound μ hAm hB hJ (mul_pos hk hN) (by
      filter_upwards [hpoint] with x hx
      by_cases hxA : x ∈ A <;> simpa only [hxA, ↓reduceIte] using hx)
    (by simpa only [μ, J, mul_assoc] using
      henergy.trans (mul_le_mul_of_nonneg_left hcost (by norm_num : (0 : ℝ) ≤ 4)))
  have hμA : μ A = boundaryArea E A := by
    change (boundaryArea E).restrict (Metric.ball 0 R) A = _
    rw [Measure.restrict_apply₀ hAm]
    congr 1
    exact inter_eq_left.mpr (fun x hx ↦ Metric.ball_subset_ball hrR hx.1)
  calc
    _ = ENNReal.ofReal (∫ x, ‖B x‖ ∂μ) := by
      symm
      simpa only [ofReal_norm] using ofReal_integral_norm_eq_lintegral_enorm hB
    _ ≤ ENNReal.ofReal (5 * (k * N) * μ.real A) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 5 * (k * N)), Measure.real,
        ENNReal.ofReal_toReal (measure_ne_top μ A), hμA, mul_assoc]

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
open scoped ENNReal Topology ContDiff
namespace RPISingularHarnack
open RPI RPI.Boundary

theorem exists_interior_cutoff_constant : ∃ L : ℝ, 0 < L ∧ ∀ (n : ℕ) (E : Set (Euc n))
    (s r : ℝ), 0 < s → s < r → ∃ η : Euc n → ℝ,
    ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ Metric.ball 0 r ∧
    (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧ (∀ x ∈ Metric.ball 0 s, η x = 1) ∧
    (∀ x, ‖tangentialGradient E η x‖ ≤ L / (r - s)) := by
  obtain ⟨M, hM, hb⟩ := exists_smoothTransition_deriv_bound
  refine ⟨8 * M, by positivity, ?_⟩
  intro n E s r hs hsr
  let b := (s + r) / 2
  have hsb : s < b := by dsimp [b]; linarith
  have hbr : b < r := by dsimp [b]; linarith
  have hb0 : 0 < b := hs.trans hsb
  let η := fun x : Euc n ↦ 1 - annularCutoff 0 s b x
  have hη : ContDiff ℝ ∞ η := contDiff_const.sub (annularCutoff_contDiff 0 s b)
  have hts : tsupport η ⊆ Metric.closedBall 0 b := by
    apply closure_minimal
    · intro x hx
      by_contra hxb
      have hdist : b ≤ dist x 0 := le_of_lt (lt_of_not_ge hxb)
      exact hx (by dsimp [η]; rw [annularCutoff_one hs hsb hdist, sub_self])
    · exact Metric.isClosed_closedBall
  have hgrad (x : Euc n) : gradient η x = -gradient (annularCutoff 0 s b) x := by
    simp only [η, gradient, fderiv_const_sub, map_neg]
  refine ⟨η, hη, (isCompact_closedBall (0 : Euc n) b).of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans (Metric.closedBall_subset_ball hbr), ?_, ?_, ?_⟩
  · intro x
    have h := annularCutoff_mem_Icc (0 : Euc n) s b x
    dsimp [η]
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  · intro x hx
    dsimp [η]
    rw [annularCutoff_zero hs hsb (Metric.mem_ball.mp hx).le, sub_zero]
  · intro x
    have hden : 0 < b ^ 2 - s ^ 2 := by nlinarith
    have hwidth : 0 < r - s := sub_pos.mpr hsr
    calc
      _ ≤ 2 * ‖gradient η x‖ := tangentialGradient_norm_le_twice E η x
      _ = 2 * ‖gradient (annularCutoff 0 s b) x‖ := by rw [hgrad, norm_neg]
      _ ≤ 2 * (2 * M * b / (b ^ 2 - s ^ 2)) :=
        mul_le_mul_of_nonneg_left (gradient_annularCutoff_bound hs hsb hM hb x) (by norm_num)
      _ ≤ 8 * M / (r - s) := by
        rw [← mul_div_assoc, div_le_div_iff₀ hden hwidth]
        have hbs : b - s = (r - s) / 2 := by dsimp [b]; ring
        have hp : 0 ≤ M * s * (r - s) := by positivity
        have heq : 8 * M * (b ^ 2 - s ^ 2) - 2 * (2 * M * b) * (r-s) = 4 * M * s * (r-s) := by
          dsimp [b]
          ring
        nlinarith

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
open scoped ENNReal Topology ContDiff
namespace RPIIteration

lemma sublevel_step_division {a b C d p : ℝ} (hd : 0 < d) (hb : 0 ≤ b)
    (h : d ^ p * a ≤ C * b ^ p) : a ≤ C * (b / d) ^ p := by
  have hdp := Real.rpow_pos_of_pos hd p
  rw [Real.div_rpow hb hd.le, ← mul_div_assoc, le_div_iff₀ hdp]
  rwa [mul_comm]

lemma sublevel_step_factor {C L k l s r a p : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hk : 0 < k) (hkl : l < k) (hsr : s < r) (ha : 0 ≤ a) :
    C * (5 * k * (L / (r-s)) * a / ((k-l) / 2)) ^ p ≤
      ((C + 1) * (10 * L) ^ p) * (k / ((r-s) * (k-l))) ^ p * a ^ p := by
  have heq : 5 * k * (L / (r-s)) * a / ((k-l)/2) =
      (10 * L) * (k / ((r-s) * (k-l))) * a := by field_simp; ring
  rw [heq, Real.mul_rpow (by positivity) ha,
    Real.mul_rpow (by positivity) (by positivity)]
  have hc : C ≤ C + 1 := by linarith
  calc
    _ ≤ (C + 1) * ((10 * L) ^ p * (k / ((r-s) * (k-l))) ^ p * a ^ p) := by
      exact mul_le_mul hc le_rfl (by positivity) (add_nonneg hC zero_le_one)
    _ = _ := by ring

end RPIIteration

end

end OAI
