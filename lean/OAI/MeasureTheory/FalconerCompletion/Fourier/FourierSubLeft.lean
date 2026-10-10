import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Fourier.Fourier

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CriticalFourierSupport
namespace CurrentFalconer
open MeasureTheory Set ComplexConjugate
open scoped ENNReal NNReal RealInnerProductSpace FourierTransform

section FourierSmoothing
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem fourier_sub_left (f : V → ℂ) (v x : V) :
    𝓕 (fun u => f (v-u)) x =
      Complex.exp ((-2 * Real.pi * ⟪v, x⟫ : ℝ) * Complex.I) * 𝓕⁻ f x := by
  rw [Real.fourier_eq']
  have h := integral_sub_left_eq_self
    (fun u : V => Complex.exp ((-2 * Real.pi * ⟪v-u, x⟫ : ℝ) * Complex.I) * f u)
    volume v
  simp only [sub_sub_cancel, smul_eq_mul] at h ⊢
  rw [h, Real.fourierInv_eq', ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [show (((-2 * Real.pi * ⟪v-u, x⟫ : ℝ) : ℂ) * Complex.I) =
    ((-2 * Real.pi * ⟪v, x⟫ : ℝ) : ℂ) * Complex.I +
      ((2 * Real.pi * ⟪u, x⟫ : ℝ) : ℂ) * Complex.I by
        rw [inner_sub_left]
        push_cast
        ring, Complex.exp_add]
  simp only [smul_eq_mul, mul_assoc]

theorem sourceFourier_reproduce (μ : Measure V) [IsFiniteMeasure μ]
    (χ : SchwartzMap V ℂ) (hχ : ∀ᵐ x ∂μ, χ x = 1) (v : V) :
    PlanarFalconer.sourceFourier μ v =
      ∫ u : V, (𝓕 χ) (v-u) * PlanarFalconer.sourceFourier μ u := by
  rw [PlanarFalconer.sourceFourier_integral_swap μ _
    ((𝓕 χ).integrable.comp_sub_left v)]
  simp_rw [fourier_sub_left]
  have hi : 𝓕⁻ ((𝓕 χ : SchwartzMap V ℂ) : V → ℂ) = (χ : V → ℂ) := by
    rw [← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq]
  rw [hi]
  unfold PlanarFalconer.sourceFourier
  rw [charFun_apply]
  apply integral_congr_ae
  filter_upwards [hχ] with x hx
  rw [hx, mul_one]
  congr 1
  rw [inner_smul_right, real_inner_comm x v]
  push_cast
  ring

theorem weighted_integral_sq_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {f k : α → ℝ} {B : ℝ} (hf : AEStronglyMeasurable f ν)
    (hk : Integrable k ν) (hf0 : ∀ x, 0 ≤ f x) (hk0 : ∀ x, 0 ≤ k x)
    (hfB : ∀ᵐ x ∂ν, f x ≤ B) :
    (∫ x, f x * k x ∂ν)^2 ≤
      (∫ x, f x^2 * k x ∂ν) * (∫ x, k x ∂ν) := by
  have hfk : Integrable (fun x => f x^2 * k x) ν := by
    apply hk.bdd_mul (hf.pow 2)
    filter_upwards [hfB] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hf0 x) hx 2
  have hkm := Real.continuous_sqrt.comp_aestronglyMeasurable hk.aestronglyMeasurable
  have hF : MemLp (fun x => f x * Real.sqrt (k x)) 2 ν := by
    apply (memLp_two_iff_integrable_sq (hf.mul hkm)).mpr
    simpa only [Pi.mul_apply, mul_pow, Real.sq_sqrt (hk0 _)] using hfk
  have hG : MemLp (fun x => Real.sqrt (k x)) 2 ν := by
    apply (memLp_two_iff_integrable_sq hkm).mpr
    simpa only [Real.sq_sqrt (hk0 _)] using hk
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all ν (fun x => mul_nonneg (hf0 x) (Real.sqrt_nonneg _)))
    (ae_of_all ν (fun x => Real.sqrt_nonneg (k x)))
    (by simpa using hF) (by simpa using hG)
  simp only [Real.rpow_two, mul_pow, ← Real.sqrt_eq_rpow, mul_assoc,
    ← pow_two, Real.sq_sqrt (hk0 _)] at h
  have h0 : 0 ≤ ∫ x, f x * k x ∂ν :=
    integral_nonneg (fun x => mul_nonneg (hf0 x) (hk0 x))
  have hI : 0 ≤ ∫ x, f x^2 * k x ∂ν :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hk0 x))
  have hJ : 0 ≤ ∫ x, k x ∂ν := integral_nonneg hk0
  have hh := pow_le_pow_left₀ h0 h 2
  simpa only [mul_pow, Real.sq_sqrt hI, Real.sq_sqrt hJ] using hh

theorem sourceFourier_sq_le_smooth (μ : Measure V) [IsFiniteMeasure μ]
    (χ : SchwartzMap V ℂ) (hχ : ∀ᵐ x ∂μ, χ x = 1) (v : V) :
    ‖PlanarFalconer.sourceFourier μ v‖^2 ≤
      (∫ u : V, ‖(𝓕 χ) u‖) *
        ∫ u : V, ‖PlanarFalconer.sourceFourier μ u‖^2 * ‖(𝓕 χ) (v-u)‖ := by
  have hI : ‖PlanarFalconer.sourceFourier μ v‖ ≤
      ∫ u : V, ‖PlanarFalconer.sourceFourier μ u‖ * ‖(𝓕 χ) (v-u)‖ := by
    rw [sourceFourier_reproduce μ χ hχ v]
    apply (norm_integral_le_integral_norm _).trans_eq
    apply integral_congr_ae
    filter_upwards with u
    rw [norm_mul, mul_comm]
  have hf : AEStronglyMeasurable
      (fun u : V => ‖PlanarFalconer.sourceFourier μ u‖) volume := by
    unfold PlanarFalconer.sourceFourier
    fun_prop
  have h := weighted_integral_sq_le volume hf
    ((𝓕 χ).integrable.norm.comp_sub_left v)
    (fun u => norm_nonneg _) (fun u => norm_nonneg _)
    (ae_of_all volume (fun u => norm_charFun_le ((-(2 * Real.pi)) • u)))
  have h' := (pow_le_pow_left₀ (norm_nonneg _) hI 2).trans h
  rw [integral_sub_left_eq_self (fun u : V => ‖(𝓕 χ : SchwartzMap V ℂ) u‖) volume v] at h'
  simpa only [mul_comm] using h'

end FourierSmoothing

theorem gaussianBallSeries_summable (S : ℝ) :
    Summable (fun n : ℕ => Real.exp (-(n : ℝ)) * ((n : ℝ)+1)^S) := by
  obtain ⟨D, hD⟩ := exists_nat_ge S
  have hr : ‖Real.exp (-1)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    norm_num
  have hg := summable_pow_mul_geometric_of_norm_lt_one D hr
  have hg' := (summable_nat_add_iff 1).2 hg
  have hh := hg'.mul_left (Real.exp 1)
  have hh' : Summable (fun n : ℕ => Real.exp (-(n : ℝ)) * ((n : ℝ)+1)^D) := by
    apply hh.congr
    intro n
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← Real.exp_nat_mul]
    rw [mul_left_comm, ← Real.exp_add, mul_comm]
    congr 2
    push_cast
    ring
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hh'
  intro n
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) hD

noncomputable def gaussianBallConstant (S : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-(n : ℝ)) * ((n : ℝ)+1)^S

theorem gaussianBallConstant_nonneg (S : ℝ) : 0 ≤ gaussianBallConstant S := by
  apply tsum_nonneg
  intro n
  positivity

section GaussianBallBound
variable {V : Type*} [PseudoMetricSpace V] [MeasurableSpace V] [BorelSpace V]

theorem gaussian_integral_le_ball_series (μ : Measure V) {S K B : ℝ}
    (hK : 0 ≤ K) (hB : 0 < B)
    (hball : ∀ (x : V) (r : ℝ), B⁻¹ ≤ r →
      μ (Metric.ball x r) ≤ ENNReal.ofReal (K * r^S)) (x : V) :
    (∫⁻ y : V, ENNReal.ofReal (Real.exp (-(B * dist x y)^2)) ∂μ) ≤
      ENNReal.ofReal (K * B^(-S)) *
        ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ)) * ((n : ℝ)+1)^S) := by
  let F : ℕ → V → ℝ≥0∞ := fun n =>
    (Metric.ball x (((n : ℝ)+1)/B)).indicator
      (fun _ => ENNReal.ofReal (Real.exp (-(n : ℝ))))
  have hF : ∀ n, AEMeasurable (F n) μ := by
    intro n
    exact (measurable_const.indicator measurableSet_ball).aemeasurable
  have hpoint : ∀ y : V, ENNReal.ofReal (Real.exp (-(B * dist x y)^2)) ≤
      ∑' n : ℕ, F n y := by
    intro y
    let n := Nat.floor (B * dist x y)
    have hn : (n : ℝ) ≤ B * dist x y := Nat.floor_le (by positivity)
    have hlt : B * dist x y < (n : ℝ)+1 := Nat.lt_floor_add_one _
    have hmem : y ∈ Metric.ball x (((n : ℝ)+1)/B) := by
      rw [Metric.mem_ball, dist_comm, lt_div_iff₀ hB]
      nlinarith
    have hsq : (n : ℝ) ≤ (B * dist x y)^2 := by
      by_cases hn0 : n = 0
      · simp only [hn0, Nat.cast_zero]
        positivity
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
        nlinarith
    calc
      ENNReal.ofReal (Real.exp (-(B * dist x y)^2)) ≤ F n y := by
        dsimp only [F]
        rw [Set.indicator_of_mem hmem]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hsq))
      _ ≤ ∑' n : ℕ, F n y := ENNReal.le_tsum (f := fun index => F index y) n
  calc
    (∫⁻ y : V, ENNReal.ofReal (Real.exp (-(B * dist x y)^2)) ∂μ) ≤
        ∫⁻ y : V, ∑' n : ℕ, F n y ∂μ := lintegral_mono hpoint
    _ = ∑' n : ℕ, ∫⁻ y : V, F n y ∂μ := lintegral_tsum hF
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (K * B^(-S)) *
        ENNReal.ofReal (Real.exp (-(n : ℝ)) * ((n : ℝ)+1)^S) := by
      apply ENNReal.tsum_le_tsum
      intro n
      dsimp only [F]
      rw [lintegral_indicator measurableSet_ball, lintegral_const, Measure.restrict_apply_univ]
      have hr : B⁻¹ ≤ ((n : ℝ)+1)/B := by
        rw [inv_eq_one_div, div_le_div_iff_of_pos_right hB]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have hb : ENNReal.ofReal (Real.exp (-(n : ℝ))) *
          μ (Metric.ball x (((n : ℝ)+1)/B)) ≤
          ENNReal.ofReal (Real.exp (-(n : ℝ))) *
            ENNReal.ofReal (K * (((n : ℝ)+1)/B)^S) := by
        gcongr
        exact hball x _ hr
      refine hb.trans_eq ?_
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg hB.le _)),
        Real.div_rpow (by positivity) hB.le, Real.rpow_neg hB.le]
      congr 1
      ring
    _ = _ := ENNReal.tsum_mul_left

theorem gaussian_integral_le_ball_bound (μ : Measure V) [IsFiniteMeasure μ]
    {S K B : ℝ} (hK : 0 ≤ K) (hB : 0 < B)
    (hball : ∀ (x : V) (r : ℝ), B⁻¹ ≤ r →
      μ (Metric.ball x r) ≤ ENNReal.ofReal (K * r^S)) (x : V) :
    (∫ y : V, Real.exp (-(B * dist x y)^2) ∂μ) ≤
      gaussianBallConstant S * K * B^(-S) := by
  have hi : Integrable (fun y : V => Real.exp (-(B * dist x y)^2)) μ := by
    apply (integrable_const (1 : ℝ)).mono (by fun_prop)
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  have h := gaussian_integral_le_ball_series μ hK hB hball x
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n : ℕ => by positivity)
    (gaussianBallSeries_summable S),
    ← ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with y; positivity),
    ← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg hB.le _))] at h
  have he : K * B^(-S) * (∑' n : ℕ, Real.exp (-(n : ℝ)) * ((n : ℝ)+1)^S) =
      gaussianBallConstant S * K * B^(-S) := by
    unfold gaussianBallConstant
    ring
  rw [he] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by
    exact mul_nonneg (mul_nonneg (gaussianBallConstant_nonneg S) hK)
      (Real.rpow_nonneg hB.le _))).mp h

omit [BorelSpace V] in

theorem probability_ball_bound_large_radii (μ : Measure V) [IsProbabilityMeasure μ]
    {S K a : ℝ} (hS : 0 ≤ S) (hK : 1 ≤ K)
    (hball : ∀ (x : V) (r : ℝ), a ≤ r → r ≤ 1 →
      μ (Metric.ball x r) ≤ ENNReal.ofReal (K * r^S)) :
    ∀ (x : V) (r : ℝ), a ≤ r →
      μ (Metric.ball x r) ≤ ENNReal.ofReal (K * r^S) := by
  intro x r hr
  by_cases hr1 : r ≤ 1
  · exact hball x r hr hr1
  · have hr1' : 1 ≤ r := le_of_not_ge hr1
    calc
      μ (Metric.ball x r) ≤ μ univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal (K * r^S) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ K * r^S := mul_le_mul hK (Real.one_le_rpow hr1' hS)
            (by norm_num) (by linarith)

end GaussianBallBound

section FourierBallBound
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem gaussian_distance_integrable (μ : Measure V) [IsFiniteMeasure μ]
    (B : ℝ) (x : V) : Integrable (fun y : V => Real.exp (-(B * dist x y)^2)) μ := by
  apply (integrable_const (1 : ℝ)).mono (by fun_prop)
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))

theorem gaussian_fourier_integral_le (μ : Measure V) [IsProbabilityMeasure μ]
    {S K B : ℝ} (hK : 0 ≤ K) (hB : 0 < B)
    (hball : ∀ (x : V) (r : ℝ), B⁻¹ ≤ r →
      μ (Metric.ball x r) ≤ ENNReal.ofReal (K * r^S)) :
    (∫ u : V, Real.exp (-(1/B^2) * ‖u‖^2) *
      ‖PlanarFalconer.sourceFourier μ u‖^2) ≤
      Real.pi^((Module.finrank ℝ V : ℝ)/2) * gaussianBallConstant S * K *
        B^((Module.finrank ℝ V : ℝ)-S) := by
  have hb : 0 < 1/B^2 := by positivity
  rw [PlanarFalconer.gaussian_lebesgue_square μ hb]
  have hinner : ∀ x : V,
      (∫ y : V, Real.exp (-(Real.pi^2/(1/B^2)) * ‖x-y‖^2) ∂μ) ≤
        gaussianBallConstant S * K * B^(-S) := by
    intro x
    apply le_trans _ (gaussian_integral_le_ball_bound μ hK hB hball x)
    apply integral_mono_of_nonneg (by filter_upwards with y; positivity)
      (gaussian_distance_integrable μ B x)
    filter_upwards with y
    apply Real.exp_le_exp.mpr
    rw [dist_eq_norm]
    have he : Real.pi^2/(1/B^2) = Real.pi^2*B^2 := by field_simp
    rw [he, mul_pow]
    have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
    nlinarith [sq_nonneg (B * ‖x-y‖), mul_nonneg (sub_nonneg.mpr hpi)
      (mul_nonneg (sq_nonneg B) (sq_nonneg ‖x-y‖))]
  have houter := integral_mono_of_nonneg
    (ae_of_all μ (fun x : V => integral_nonneg (fun y : V => (Real.exp_pos _).le)))
    (integrable_const (gaussianBallConstant S * K * B^(-S)))
    (ae_of_all μ hinner)
  simp only [integral_const, probReal_univ, one_smul] at houter
  have h := mul_le_mul_of_nonneg_left houter
    (Real.rpow_nonneg (div_nonneg Real.pi_pos.le hb.le) (Module.finrank ℝ V / 2 : ℝ))
  refine h.trans_eq ?_
  have he : Real.pi/(1/B^2) = Real.pi * B^2 := by field_simp
  rw [he, Real.mul_rpow Real.pi_pos.le (sq_nonneg B)]
  have hp : (B^2)^((Module.finrank ℝ V : ℝ)/2) = B^(Module.finrank ℝ V : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hB.le]
    congr 1
    ring
  rw [hp, sub_eq_add_neg, Real.rpow_add hB]
  ring

theorem fourier_ball_integral_le (μ : Measure V) [IsProbabilityMeasure μ]
    {S K B : ℝ} (hK : 0 ≤ K) (hB : 0 < B)
    (hball : ∀ (x : V) (r : ℝ), B⁻¹ ≤ r →
      μ (Metric.ball x r) ≤ ENNReal.ofReal (K * r^S)) :
    (∫ u : V in Metric.ball 0 (4*B), ‖PlanarFalconer.sourceFourier μ u‖^2) ≤
      Real.exp 16 * Real.pi^((Module.finrank ℝ V : ℝ)/2) *
        gaussianBallConstant S * K * B^((Module.finrank ℝ V : ℝ)-S) := by
  have hi := PlanarFalconer.gaussian_sourceFourier_integrable μ
    (show 0 < 1/B^2 by positivity)
  have hpoint : ∀ u : V, u ∈ Metric.ball 0 (4*B) →
      ‖PlanarFalconer.sourceFourier μ u‖^2 ≤
        Real.exp 16 * (Real.exp (-(1/B^2) * ‖u‖^2) *
          ‖PlanarFalconer.sourceFourier μ u‖^2) := by
    intro u hu
    have hn : ‖u‖ < 4*B := by simpa only [Metric.mem_ball, dist_zero_right] using hu
    have hx : -(1/B^2)*‖u‖^2 + 16 ≥ 0 := by
      have hs : ‖u‖^2 ≤ 16*B^2 := by nlinarith [norm_nonneg u]
      have hd := (div_le_iff₀ (sq_pos_of_pos hB)).mpr hs
      have he : -(1/B^2)*‖u‖^2 + 16 = 16 - ‖u‖^2/B^2 := by ring
      rw [he]
      linarith
    have he : 1 ≤ Real.exp 16 * Real.exp (-(1/B^2)*‖u‖^2) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (sq_nonneg
      ‖PlanarFalconer.sourceFourier μ u‖)]
  have h₁ : (∫ u : V in Metric.ball 0 (4*B), ‖PlanarFalconer.sourceFourier μ u‖^2) ≤
      ∫ u : V in Metric.ball 0 (4*B), Real.exp 16 *
        (Real.exp (-(1/B^2)*‖u‖^2)*‖PlanarFalconer.sourceFourier μ u‖^2) := by
    apply integral_mono_of_nonneg (by filter_upwards with u; positivity)
      ((hi.const_mul _).integrableOn)
    filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
    exact hpoint u hu
  have h₂ := setIntegral_le_integral (s := Metric.ball 0 (4*B)) (hi.const_mul (Real.exp 16))
    (by filter_upwards with u; positivity)
  apply (h₁.trans h₂).trans
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (gaussian_fourier_integral_le μ hK hB hball)
    (Real.exp_pos 16).le
  convert h using 1
  ring

end FourierBallBound
end CurrentFalconer
end CriticalFourierSupport
end
end

end OAI
