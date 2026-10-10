import Mathlib
import OAI.Geometry.SmoothYau.Estimates.PartialBilinearExtension
import OAI.Geometry.SmoothYau.Spectrum.AnisotropicConstant

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
namespace YauCounterexamples

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def boundedDistribution (f : E →ᵇ F) : 𝓢'(E, F) :=
  ((f.memLp_top (μ := volume)).toLp f : 𝓢'(E, F))

lemma boundedDistribution_apply (f : E →ᵇ F) (φ : 𝓢(E, ℂ)) :
    boundedDistribution f φ = ∫ x, φ x • f x := by
  rw [boundedDistribution, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(f.memLp_top (μ := volume)).coeFn_toLp] with x hx
  rw [hx]

def inverseFourierL1 (v : Lp F 1 (volume : Measure E)) : E →ᵇ F :=
  (Real.Lp.fourierTransform v).compContinuous ⟨fun x => -x, continuous_neg⟩

omit [CompleteSpace F] in
lemma inverseFourierL1_apply (v : Lp F 1 (volume : Measure E)) (x : E) :
    inverseFourierL1 v x = 𝓕⁻ (v : E → F) x := by
  exact (Real.fourierInv_eq_fourier_neg _ _).symm

theorem inverseFourierL1_distribution (v : Lp F 1 (volume : Measure E)) :
    boundedDistribution (inverseFourierL1 v) = 𝓕⁻ (v : 𝓢'(E, F)) := by
  ext φ
  rw [boundedDistribution_apply, TemperedDistribution.fourierInv_apply,
    Lp.toTemperedDistribution_apply]
  simp only [inverseFourierL1_apply, SchwartzMap.fourierInv_coe]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := (volume : Measure E)) (ν := (volume : Measure E))
    (L := -innerₗ E) (f := (φ : E → ℂ)) (g := (v : E → F))
    Real.continuous_fourierChar (innerSL ℝ).continuous₂.neg φ.integrable
    (L1.integrable_coeFn v)
  have hflip : (-innerₗ E).flip = -innerₗ E := by
    ext x y
    exact congrArg Neg.neg (real_inner_comm y x).symm
  rw [hflip] at h
  exact h.symm

theorem sobolev_continuous_representative {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s) (f : 𝓢'(E, F))
    (hf : MemSobolev s 2 f) :
    ∃ u : E →ᵇ F, boundedDistribution u = f := by
  obtain ⟨v, hv⟩ := hf.fourier_memL1 hs
  refine ⟨inverseFourierL1 v, ?_⟩
  rw [inverseFourierL1_distribution, ← hv, fourierInv_fourier_eq]

lemma memLp_bessel_weight {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    MemLp (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 := by
  have hgrowth : (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
    fun_prop
  rw [MemLp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
    hgrowth.1.continuous.aestronglyMeasurable]
  suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
    norm_cast
    simp_rw [ofReal_norm] at h
    simp_rw [← enorm_pow]
    convert h using 1
    congr 1
    ext x
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 2
    ring
  apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  congr
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_pow_mul_bessel_weight_le (x : E) (n : ℕ) (s : ℝ) :
    ‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2) ≤
      (1 + ‖x‖ ^ 2) ^ (-(s - n) / 2) := by
  have hp : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hnorm : ‖x‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := by
    apply (Real.le_sqrt (norm_nonneg _) (le_of_lt hp)).mpr
    linarith
  calc
    _ ≤ (Real.sqrt (1 + ‖x‖ ^ 2)) ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2) := by
      gcongr
    _ = (1 + ‖x‖ ^ 2) ^ (-(s - n) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hp.le, ← Real.rpow_add hp]
      congr 1
      ring

lemma memLp_moment_bessel_weight {s : ℝ} (n : ℕ)
    (hs : Module.finrank ℝ E < 2 * (s - n)) :
    MemLp (fun x : E ↦ ‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 := by
  refine (memLp_bessel_weight hs).mono' ?_ ?_
  · have ht : (fun x : E => (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
      fun_prop
    exact ((continuous_norm.pow n).mul ht.1.continuous).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact norm_pow_mul_bessel_weight_le x n s

theorem sobolev_fourier_moments {s : ℝ} (N : ℕ)
    (hs : Module.finrank ℝ E < 2 * (s - N)) (f : 𝓢'(E, F))
    (hf : MemSobolev s 2 f) :
    ∃ v : Lp F 1 (volume : Measure E), 𝓕 f = (v : 𝓢'(E, F)) ∧
      ∀ n ≤ N, Integrable (fun x : E => ‖x‖ ^ n * ‖v x‖) := by
  obtain ⟨u, hu⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hf
  have hdim : (Module.finrank ℝ E : ℝ) < 2 * s := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hw : MemLp (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) 2 :=
    (memLp_bessel_weight hdim).ofReal
  let v : Lp F 1 (volume : Measure E) := hw.toLp _ • u
  refine ⟨v, ?_, ?_⟩
  · dsimp [v]
    rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq]
    · rw [← hu, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
      convert (smulLeftCLM_const 1 (𝓕 f)).symm using 1
      · simp
      · congr
        ext x
        rw [Pi.mul_apply]
        norm_cast
        rw [← Real.rpow_add (by positivity)]
        ring_nf
        simp
    · fun_prop
  · intro n hn
    have hsn : (Module.finrank ℝ E : ℝ) < 2 * (s - n) := by
      have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
      linarith
    have hm : MemLp (fun x : E =>
        (‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2)) * ‖u x‖) 1 :=
      (memLp_moment_bessel_weight n hsn).fun_mul (Lp.memLp u).norm
    apply (memLp_one_iff_integrable.mp hm).congr
    filter_upwards [Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) (hw.toLp _) u,
      hw.coeFn_toLp] with x hx hy
    change _ = ‖x‖ ^ n * ‖(hw.toLp _ • u : Lp F 1 volume) x‖
    rw [hx]
    change _ = ‖x‖ ^ n * ‖(hw.toLp _ : E → ℂ) x • u x‖
    rw [hy]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2) (-s / 2))]
    ring

theorem sobolev_Ck_representative {s : ℝ} (N : ℕ)
    (hs : Module.finrank ℝ E < 2 * (s - N)) (f : 𝓢'(E, F))
    (hf : MemSobolev s 2 f) :
    ∃ u : E →ᵇ F, boundedDistribution u = f ∧ ContDiff ℝ N (u : E → F) := by
  obtain ⟨v, hv, hm⟩ := sobolev_fourier_moments N hs f hf
  refine ⟨inverseFourierL1 v, ?_, ?_⟩
  · rw [inverseFourierL1_distribution, ← hv, fourierInv_fourier_eq]
  · have hd : ContDiff ℝ N (𝓕 (v : E → F)) :=
      Real.contDiff_fourier (fun n hn => hm n (by exact_mod_cast hn))
    change ContDiff ℝ N (fun x : E => 𝓕 (v : E → F) (-x))
    exact hd.comp contDiff_neg

theorem boundedDistribution_injective :
    Function.Injective (boundedDistribution (E := E) (F := F)) := by
  intro u v huv
  have hi : Function.Injective
      (Lp.toTemperedDistributionCLM F (volume : Measure E) ∞) :=
    LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
  have hLp : (u.memLp_top (μ := volume)).toLp u =
      (v.memLp_top (μ := volume)).toLp v := hi huv
  apply DFunLike.ext'
  apply Measure.eq_of_ae_eq (μ := (volume : Measure E)) _ u.continuous v.continuous
  exact ((u.memLp_top (μ := volume)).coeFn_toLp).symm.trans
    ((Filter.EventuallyEq.of_eq (congrArg (fun z : Lp F ∞ (volume : Measure E) =>
      (z : E → F)) hLp)).trans (v.memLp_top (μ := volume)).coeFn_toLp)

theorem sobolev_smooth_representative (f : 𝓢'(E, F))
    (hf : ∀ n : ℕ, MemSobolev n 2 f) :
    ∃ u : E →ᵇ F, boundedDistribution u = f ∧ ContDiff ℝ ∞ (u : E → F) := by
  obtain ⟨u, hu, _⟩ := sobolev_Ck_representative 0
    (s := (Module.finrank ℝ E + 1 : ℕ)) (by push_cast; simp; linarith) f
    (hf (Module.finrank ℝ E + 1))
  refine ⟨u, hu, contDiff_infty.mpr ?_⟩
  intro n
  obtain ⟨v, hv, hdiff⟩ := sobolev_Ck_representative n
    (s := (Module.finrank ℝ E + n + 1 : ℕ)) (by push_cast; linarith) f
    (hf (Module.finrank ℝ E + n + 1))
  have huv := boundedDistribution_injective (hu.trans hv.symm)
  rwa [huv]

omit [CompleteSpace F] in

lemma norm_inverseFourierL1_le (v : Lp F 1 (volume : Measure E)) :
    ‖inverseFourierL1 v‖ ≤ ‖v‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg v)]
  intro x
  change ‖𝓕 (v : E → F) (-x)‖ ≤ ‖v‖
  rw [Real.fourier_eq]
  apply (norm_integral_le_integral_norm _).trans
  simp_rw [Circle.norm_smul]
  exact (L1.norm_eq_integral_norm v).symm.le

theorem sobolev_quantitative_representative {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s) (f : 𝓢'(E, F))
    (v : Lp F 2 (volume : Measure E))
    (hv : smulLeftCLM F (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2)))
      (𝓕 f) = (v : 𝓢'(E, F))) :
    ∃ u : E →ᵇ F, boundedDistribution u = f ∧
      ‖u‖ ≤ ‖((memLp_bessel_weight hs).ofReal :
        MemLp (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) 2).toLp _‖ * ‖v‖ := by
  have hw : MemLp (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) 2 :=
    (memLp_bessel_weight hs).ofReal
  let w : Lp F 1 (volume : Measure E) := hw.toLp _ • v
  refine ⟨inverseFourierL1 w, ?_, ?_⟩
  · rw [inverseFourierL1_distribution]
    dsimp [w]
    rw [Lp.toTemperedDistribution_smul_eq (by fun_prop), ← hv,
      smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    have heq : (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2))) *
        (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) = (fun _ => 1) := by
      ext x
      simp only [Pi.mul_apply]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      convert Real.rpow_zero _ using 2
      ring
    rw [heq, smulLeftCLM_const]
    simp
  · exact (norm_inverseFourierL1_le w).trans (Lp.norm_smul_le (hw.toLp _) v)

end YauCounterexamples

open MeasureTheory
open scoped ENNReal

end

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples

lemma lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x * g x ∂μ) ^ (2 : ℕ) ≤
      (∫⁻ x, f x ∂μ) * ∫⁻ x, f x * g x ^ (2 : ℕ) ∂μ := by
  have h := ENNReal.lintegral_mul_norm_pow_le hf (hf.mul (hg.pow_const (2 : ℕ)))
    (p := (1 / 2 : ℝ)) (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have heq : (fun x => f x ^ (1 / 2 : ℝ) * (f x * g x ^ (2 : ℕ)) ^ (1 / 2 : ℝ)) =
      fun x => f x * g x := by
    ext x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_assoc,
      ← ENNReal.rpow_add_of_nonneg (1 / 2) (1 / 2) (by norm_num) (by norm_num)]
    norm_num [← ENNReal.rpow_natCast_mul]
  simp only [Pi.mul_apply] at h
  rw [heq] at h
  have hs := pow_le_pow_left' h 2
  simpa [mul_pow, ← ENNReal.rpow_mul_natCast] using hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem young_lintegral_sq {f g : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, (∫⁻ y, f y * g (x - y)) ^ (2 : ℕ)) ≤
      (∫⁻ y, f y) ^ (2 : ℕ) * ∫⁻ x, g x ^ (2 : ℕ) := by
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, f y) * ∫⁻ y, f y * g (x - y) ^ (2 : ℕ) := by
      apply lintegral_mono
      intro x
      exact lintegral_mul_sq_le volume hf.aemeasurable (by fun_prop)
    _ = (∫⁻ y, f y) * ∫⁻ x, ∫⁻ y, f y * g (x - y) ^ (2 : ℕ) := by
      rw [lintegral_const_mul'' _ (by fun_prop)]
    _ = (∫⁻ y, f y) * ∫⁻ y, ∫⁻ x, f y * g (x - y) ^ (2 : ℕ) := by
      rw [lintegral_lintegral_swap (by fun_prop)]
    _ = (∫⁻ y, f y) ^ (2 : ℕ) * ∫⁻ x, g x ^ (2 : ℕ) := by
      have hmeas (y : E) : AEMeasurable (fun x : E => g (x - y) ^ (2 : ℕ)) volume :=
        ((hg.comp (measurable_id.sub_const y)).pow_const 2).aemeasurable
      have hshift (y : E) : (∫⁻ x, g (x - y) ^ (2 : ℕ)) = ∫⁻ x, g x ^ (2 : ℕ) :=
        lintegral_sub_right_eq_self (fun x => g x ^ (2 : ℕ)) y
      simp_rw [lintegral_const_mul'' _ (hmeas _), hshift]
      rw [lintegral_mul_const'' _ hf.aemeasurable]
      ring

theorem young_eLpNorm_two {𝕜 : Type*} [RCLike 𝕜] {f g : E → 𝕜} (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (fun x => ∫ y, f y * g (x - y)) 2 volume ≤
      eLpNorm f 1 volume * eLpNorm g 2 volume := by
  have hmeas : StronglyMeasurable (Function.uncurry (fun x y : E => f y * g (x - y))) :=
    ((hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  have hpoint (x : E) : ‖∫ y, f y * g (x - y)‖ₑ ≤ ∫⁻ y, ‖f y‖ₑ * ‖g (x - y)‖ₑ := by
    simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm
      (fun y => f y * g (x - y))
  have hsq : (∫⁻ x, ‖∫ y, f y * g (x - y)‖ₑ ^ (2 : ℕ)) ≤
      (∫⁻ y, ‖f y‖ₑ) ^ (2 : ℕ) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) := by
    exact (lintegral_mono fun x => pow_le_pow_left' (hpoint x) 2).trans
      (young_lintegral_sq hf.enorm hg.enorm)
  have hh := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast_mul] at hh
  norm_num only [Nat.cast_ofNat, mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0),
    ENNReal.rpow_one] at hh
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hmeas.integral_prod_right.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hg.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (1 : ℝ≥0∞) ≠ 0)
      (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hf.aestronglyMeasurable,
    ENNReal.toReal_ofNat, ENNReal.toReal_one, one_div_one, ENNReal.rpow_one,
    ENNReal.rpow_ofNat] using hh

theorem young_memLp_two {𝕜 : Type*} [RCLike 𝕜] {f g : E → 𝕜} (hf : Measurable f) (hg : Measurable g)
    (hf1 : MemLp f 1 volume) (hg2 : MemLp g 2 volume) :
    MemLp (fun x => ∫ y, f y * g (x - y)) 2 volume := by
  exact (young_eLpNorm_two hf hg).trans_lt
    (ENNReal.mul_lt_top hf1.eLpNorm_lt_top hg2.eLpNorm_lt_top)

def sobolevWeight (s : ℝ) (x : E) : ℝ := (1 + ‖x‖ ^ 2) ^ (s / 2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sobolevWeight_pos (s : ℝ) (x : E) : 0 < sobolevWeight s x := by
  exact Real.rpow_pos_of_pos (by positivity) _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[fun_prop] lemma continuous_sobolevWeight (s : ℝ) :
    Continuous (sobolevWeight (E := E) s) := by
  unfold sobolevWeight
  exact (continuous_const.add (continuous_norm.pow 2)).rpow_const (fun x => Or.inl (by change 1 + ‖x‖ ^ 2 ≠ 0; positivity))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sobolevWeight_add_le {s : ℝ} (hs : 0 ≤ s) (x y : E) :
    sobolevWeight s (x + y) ≤ (4 : ℝ) ^ (s / 2) *
      (sobolevWeight s x + sobolevWeight s y) := by
  have hq : 1 + ‖x + y‖ ^ 2 ≤ 4 * max (1 + ‖x‖ ^ 2) (1 + ‖y‖ ^ 2) := by
    have hnorm := norm_add_le x y
    have hsq : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hx := le_max_left (1 + ‖x‖ ^ 2) (1 + ‖y‖ ^ 2)
    have hy := le_max_right (1 + ‖x‖ ^ 2) (1 + ‖y‖ ^ 2)
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have hm : 0 ≤ max (1 + ‖x‖ ^ 2) (1 + ‖y‖ ^ 2) := le_trans (by positivity) (le_max_left _ _)
  have hh := Real.rpow_le_rpow (by positivity) hq (by positivity : 0 ≤ s / 2)
  rw [Real.mul_rpow (by norm_num) hm,
    Real.rpow_max (by positivity) (by positivity) (by positivity)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (max_le (le_add_of_nonneg_right (le_of_lt (sobolevWeight_pos s y)))
      (le_add_of_nonneg_left (le_of_lt (sobolevWeight_pos s x)))) (by positivity))

open scoped SchwartzMap

def weightedSchwartz (s : ℝ) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : E => Complex.ofReal (sobolevWeight s x)) f

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weightedSchwartz_apply (s : ℝ) (f : 𝓢(E, ℂ)) (x : E) :
    weightedSchwartz s f x = Complex.ofReal (sobolevWeight s x) * f x := by
  unfold weightedSchwartz
  rw [SchwartzMap.smulLeftCLM_apply_apply]
  · rfl
  · unfold sobolevWeight
    fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_weightedSchwartz (s : ℝ) (f : 𝓢(E, ℂ)) (x : E) :
    ‖weightedSchwartz s f x‖ = sobolevWeight s x * ‖f x‖ := by
  rw [weightedSchwartz_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sobolevWeight_pos s x)]

lemma integrable_sobolevWeight_norm (s : ℝ) (f : 𝓢(E, ℂ)) :
    Integrable (fun x => sobolevWeight s x * ‖f x‖) volume := by
  simpa only [norm_weightedSchwartz] using (weightedSchwartz s f).integrable.norm

lemma integrable_norm_mul_sub (f g : 𝓢(E, ℂ)) (x : E) :
    Integrable (fun y => ‖f y‖ * ‖g (x - y)‖) volume := by
  apply f.integrable.norm.mul_bdd
  · exact (g.continuous.comp (continuous_const.sub continuous_id)).norm.aestronglyMeasurable
  · filter_upwards with y
    simpa only [norm_norm] using SchwartzMap.norm_le_seminorm ℝ g (x - y)

lemma weighted_convolution_pointwise {s : ℝ} (hs : 0 ≤ s) (f g : 𝓢(E, ℂ)) (x : E) :
    sobolevWeight s x * ‖∫ y, f y * g (x - y)‖ ≤
      (4 : ℝ) ^ (s / 2) *
        ((∫ y, ‖weightedSchwartz s f y‖ * ‖g (x - y)‖) +
         (∫ y, ‖f y‖ * ‖weightedSchwartz s g (x - y)‖)) := by
  have h1 := integrable_norm_mul_sub (weightedSchwartz s f) g x
  have h2 := integrable_norm_mul_sub f (weightedSchwartz s g) x
  have hm := (h1.add h2).const_mul ((4 : ℝ) ^ (s / 2))
  simp only [Pi.add_apply] at hm
  have hh := norm_integral_le_of_norm_le (f := fun y => sobolevWeight s x • (f y * g (x - y))) hm
    (by
      filter_upwards with y
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sobolevWeight_pos s x), norm_mul,
        norm_weightedSchwartz, norm_weightedSchwartz]
      have hw := sobolevWeight_add_le hs y (x - y)
      rw [add_sub_cancel] at hw
      calc
        _ ≤ ((4 : ℝ) ^ (s / 2) * (sobolevWeight s y + sobolevWeight s (x - y))) *
            (‖f y‖ * ‖g (x - y)‖) :=
          mul_le_mul_of_nonneg_right hw (by positivity)
        _ = _ := by ring)
  rw [integral_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (sobolevWeight_pos s x),
    integral_const_mul, integral_add h1 h2] at hh
  exact hh

lemma stronglyMeasurable_mulConvolution {𝕜 : Type*} [RCLike 𝕜] {f g : E → 𝕜}
    (hf : Measurable f) (hg : Measurable g) :
    StronglyMeasurable (fun x => ∫ y, f y * g (x - y)) := by
  have hm : StronglyMeasurable (Function.uncurry (fun x y : E => f y * g (x - y))) := by
    apply Measurable.stronglyMeasurable
    exact (hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))
  exact hm.integral_prod_right

lemma mulConvolution_comm {𝕜 : Type*} [RCLike 𝕜] (f g : E → 𝕜) (x : E) :
    (∫ y, f y * g (x - y)) = ∫ y, g y * f (x - y) := by
  rw [← integral_sub_left_eq_self (fun y => f y * g (x - y)) volume x]
  simp_rw [sub_sub_self, mul_comm]

theorem weighted_convolution_eLpNorm {s : ℝ} (hs : 0 ≤ s) (f g : 𝓢(E, ℂ)) :
    eLpNorm (fun x => sobolevWeight s x • (∫ y, f y * g (x - y))) 2 volume ≤
      ‖((4 : ℝ) ^ (s / 2))‖ₑ *
        (eLpNorm g 1 volume * eLpNorm (weightedSchwartz s f) 2 volume +
         eLpNorm f 1 volume * eLpNorm (weightedSchwartz s g) 2 volume) := by
  let q₁ : E → ℝ := fun x => ∫ y, ‖g y‖ * ‖weightedSchwartz s f (x - y)‖
  let q₂ : E → ℝ := fun x => ∫ y, ‖f y‖ * ‖weightedSchwartz s g (x - y)‖
  have hbound : eLpNorm (fun x => sobolevWeight s x • (∫ y, f y * g (x - y))) 2 volume ≤
      eLpNorm (((4 : ℝ) ^ (s / 2)) • (q₁ + q₂)) 2 volume := by
    apply eLpNorm_mono ((continuous_sobolevWeight s).aestronglyMeasurable.smul
      (stronglyMeasurable_mulConvolution f.continuous.measurable
        g.continuous.measurable).aestronglyMeasurable)
    intro x
    have hpoint := weighted_convolution_pointwise hs f g x
    rw [mulConvolution_comm (fun y => ‖weightedSchwartz s f y‖) (fun y => ‖g y‖) x] at hpoint
    change ‖sobolevWeight s x • (∫ y, f y * g (x - y))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sobolevWeight_pos s x)]
    simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ (4 : ℝ) ^ (s / 2) * (q₁ x + q₂ x) from
        mul_nonneg (by positivity) (add_nonneg (integral_nonneg (fun _ => by positivity))
          (integral_nonneg (fun _ => by positivity))))] using hpoint
  have h₁ : eLpNorm q₁ 2 volume ≤ eLpNorm g 1 volume * eLpNorm (weightedSchwartz s f) 2 volume := by
    simpa only [eLpNorm_norm _ g.continuous.aestronglyMeasurable,
      eLpNorm_norm _ (weightedSchwartz s f).continuous.aestronglyMeasurable] using
      young_eLpNorm_two g.continuous.norm.measurable
      (weightedSchwartz s f).continuous.norm.measurable
  have h₂ : eLpNorm q₂ 2 volume ≤ eLpNorm f 1 volume * eLpNorm (weightedSchwartz s g) 2 volume := by
    simpa only [eLpNorm_norm _ f.continuous.aestronglyMeasurable,
      eLpNorm_norm _ (weightedSchwartz s g).continuous.aestronglyMeasurable] using
      young_eLpNorm_two f.continuous.norm.measurable
      (weightedSchwartz s g).continuous.norm.measurable
  refine hbound.trans ?_
  rw [eLpNorm_const_smul]
  exact mul_le_mul' le_rfl ((eLpNorm_add_le
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add h₁ h₂))

lemma memLp_inverse_sobolevWeight {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    MemLp (sobolevWeight (-s) : E → ℝ) 2 volume := by
  rw [MemLp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
    (continuous_sobolevWeight (-s)).aestronglyMeasurable]
  suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
    norm_cast
    simp_rw [ofReal_norm] at h
    simp_rw [← enorm_pow]
    convert h using 1
    congr 1
    ext x
    rw [sobolevWeight, ← Real.rpow_mul_natCast (by positivity)]
    congr 2
    ring
  apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  congr
  ring

lemma schwartz_eLpNorm_one_le_weighted (s : ℝ) (f : 𝓢(E, ℂ)) :
    eLpNorm f 1 volume ≤ eLpNorm (sobolevWeight (-s) : E → ℝ) 2 volume *
      eLpNorm (weightedSchwartz s f) 2 volume := by
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    (μ := (volume : Measure E))
    (f := fun x => ‖weightedSchwartz s f x‖)
    (φ := sobolevWeight (-s))
    (continuous_sobolevWeight (-s)).aestronglyMeasurable
    (weightedSchwartz s f).continuous.norm.aestronglyMeasurable
  have heq : (sobolevWeight (-s) : E → ℝ) • (fun x => ‖weightedSchwartz s f x‖) =
      fun x => ‖f x‖ := by
    ext x
    change sobolevWeight (-s) x * ‖weightedSchwartz s f x‖ = ‖f x‖
    rw [norm_weightedSchwartz]
    unfold sobolevWeight
    rw [← mul_assoc, ← Real.rpow_add (by positivity)]
    have hexp : -s / 2 + s / 2 = 0 := by ring
    rw [hexp, Real.rpow_zero, one_mul]
  rw [heq, eLpNorm_norm _ f.continuous.aestronglyMeasurable,
    eLpNorm_norm _ (weightedSchwartz s f).continuous.aestronglyMeasurable] at h
  exact h

theorem weighted_convolution_algebra_eLpNorm {s : ℝ} (hs : 0 ≤ s) (f g : 𝓢(E, ℂ)) :
    eLpNorm (fun x => sobolevWeight s x • (∫ y, f y * g (x - y))) 2 volume ≤
      (‖((4 : ℝ) ^ (s / 2))‖ₑ * 2 * eLpNorm (sobolevWeight (-s) : E → ℝ) 2 volume) *
        eLpNorm (weightedSchwartz s f) 2 volume * eLpNorm (weightedSchwartz s g) 2 volume := by
  refine (weighted_convolution_eLpNorm hs f g).trans ?_
  have hf := schwartz_eLpNorm_one_le_weighted s f
  have hg := schwartz_eLpNorm_one_le_weighted s g
  calc
    _ ≤ ‖((4 : ℝ) ^ (s / 2))‖ₑ *
        ((eLpNorm (sobolevWeight (-s) : E → ℝ) 2 volume * eLpNorm (weightedSchwartz s g) 2 volume) *
          eLpNorm (weightedSchwartz s f) 2 volume +
        (eLpNorm (sobolevWeight (-s) : E → ℝ) 2 volume * eLpNorm (weightedSchwartz s f) 2 volume) *
          eLpNorm (weightedSchwartz s g) 2 volume) := by gcongr
    _ = _ := by ring

open FourierTransform

lemma schwartz_fourierInv_convolution (f g : 𝓢(E, ℂ)) :
    𝓕⁻ (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g) =
      SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ f) (𝓕⁻ g) := by
  ext x
  simp only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
    ← SchwartzMap.fourier_coe, SchwartzMap.fourier_convolution,
    SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply']

lemma schwartz_fourier_product (f g : 𝓢(E, ℂ)) :
    𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g) := by
  have h := schwartz_fourierInv_convolution (𝓕 f) (𝓕 g)
  simpa only [fourierInv_fourier_eq, fourier_fourierInv_eq] using
    (congrArg (fun u : 𝓢(E, ℂ) => 𝓕 u) h).symm

end YauCounterexamples

end

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
open FourierTransform MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def schwartzToSobolev (s : ℝ) : 𝓢(E, ℂ) →L[ℂ] FourierSobolevSpace E ℂ s :=
  SchwartzMap.toLpCLM ℂ ℂ 2 volume ∘L
    SchwartzMap.smulLeftCLM ℂ (fun x : E => Complex.ofReal (sobolevWeight s x)) ∘L
    fourierCLM ℂ 𝓢(E, ℂ)

lemma schwartzToSobolev_apply (s : ℝ) (f : 𝓢(E, ℂ)) :
    schwartzToSobolev s f = (weightedSchwartz s (𝓕 f)).toLp 2 volume := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weightedSchwartz_neg_cancel (s : ℝ) (f : 𝓢(E, ℂ)) :
    weightedSchwartz s (weightedSchwartz (-s) f) = f := by
  ext x
  rw [weightedSchwartz_apply, weightedSchwartz_apply, ← mul_assoc,
    ← Complex.ofReal_mul]
  have h : sobolevWeight s x * sobolevWeight (-s) x = 1 := by
    unfold sobolevWeight
    rw [← Real.rpow_add (by positivity)]
    convert Real.rpow_zero _ using 2
    ring
  rw [h, Complex.ofReal_one, one_mul]

lemma denseRange_schwartzToSobolev (s : ℝ) :
    DenseRange (schwartzToSobolev (E := E) s) := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  apply hd.mono
  rintro _ ⟨f, rfl⟩
  refine ⟨𝓕⁻ (weightedSchwartz (-s) f), ?_⟩
  rw [schwartzToSobolev_apply, fourier_fourierInv_eq, weightedSchwartz_neg_cancel]
  rfl

lemma schwartz_smul_distribution (b : E → ℂ) (hb : b.HasTemperateGrowth)
    (f : 𝓢(E, ℂ)) :
    smulLeftCLM ℂ b (f : 𝓢'(E, ℂ)) =
      (SchwartzMap.smulLeftCLM ℂ b f : 𝓢'(E, ℂ)) := by
  ext φ
  simp only [smulLeftCLM_apply_apply, SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [SchwartzMap.smulLeftCLM_apply_apply hb, smul_eq_mul]
  ring

lemma schwartzToSobolev_distribution (s : ℝ) (f : 𝓢(E, ℂ)) :
    fourierSobolevDistribution E ℂ s (schwartzToSobolev s f) = (f : 𝓢'(E, ℂ)) := by
  rw [schwartzToSobolev_apply, fourierSobolevDistribution_apply,
    Lp.toTemperedDistribution_toLp_eq]
  rw [schwartz_smul_distribution _ (by fun_prop)]
  change 𝓕⁻ ((weightedSchwartz (-s) (weightedSchwartz s (𝓕 f))) : 𝓢'(E, ℂ)) = _
  have h := weightedSchwartz_neg_cancel (-s) (𝓕 f)
  simp only [neg_neg] at h
  rw [h, TemperedDistribution.fourierInv_toTemperedDistributionCLM_eq, fourierInv_fourier_eq]

def sobolevAlgebraConstant (s : ℝ) : ℝ :=
  ((‖((4 : ℝ) ^ (s / 2))‖ₑ * 2 *
    eLpNorm (sobolevWeight (-s) : E → ℝ) 2 volume)).toReal

lemma sobolevAlgebraConstant_nonneg (s : ℝ) : 0 ≤ sobolevAlgebraConstant (E := E) s :=
  ENNReal.toReal_nonneg

lemma schwartz_sobolev_product_bound {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (f g : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev s (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g)‖ ≤
      sobolevAlgebraConstant (E := E) s * ‖schwartzToSobolev s f‖ *
        ‖schwartzToSobolev s g‖ := by
  have hs0 : 0 ≤ s := by have := (Nat.cast_nonneg (Module.finrank ℝ E) : (0 : ℝ) ≤ _); linarith
  have hb := weighted_convolution_algebra_eLpNorm hs0 (𝓕 f) (𝓕 g)
  have hw : (fun x => sobolevWeight s x • (∫ y, (𝓕 f) y * (𝓕 g) (x - y))) =
      (weightedSchwartz s (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g)) : E → ℂ) := by
    ext x
    rw [weightedSchwartz_apply]
    simp only [SchwartzMap.convolution_apply, MeasureTheory.convolution,
      ContinuousLinearMap.mul_apply']
    exact Complex.real_smul
  rw [hw, ← schwartz_fourier_product f g] at hb
  have hfin : (‖((4 : ℝ) ^ (s / 2))‖ₑ * 2 * eLpNorm (sobolevWeight (-s) : E → ℝ) 2 volume) *
        eLpNorm (weightedSchwartz s (𝓕 f)) 2 volume *
        eLpNorm (weightedSchwartz s (𝓕 g)) 2 volume ≠ ⊤ := by
    apply ENNReal.mul_ne_top _ (SchwartzMap.memLp _ _ _).eLpNorm_ne_top
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by finiteness) (memLp_inverse_sobolevWeight hs).eLpNorm_ne_top)
      (SchwartzMap.memLp _ _ _).eLpNorm_ne_top
  have hr := ENNReal.toReal_mono hfin hb
  simpa only [schwartzToSobolev_apply, SchwartzMap.norm_toLp,
    ENNReal.toReal_mul, sobolevAlgebraConstant] using hr

def schwartzSobolevProduct (s : ℝ) :
    𝓢(E, ℂ) →ₗ[ℂ] 𝓢(E, ℂ) →ₗ[ℂ] FourierSobolevSpace E ℂ s where
  toFun f := (schwartzToSobolev s).toLinearMap.comp
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f).toLinearMap
  map_add' f g := by ext h; simp
  map_smul' c f := by ext h; simp

def sobolevProduct {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    FourierSobolevSpace E ℂ s →L[ℂ]
      FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ s :=
  bilinearExtension (schwartzSobolevProduct s) (schwartzToSobolev s).toLinearMap
    (denseRange_schwartzToSobolev s) (sobolevAlgebraConstant (E := E) s)
    (schwartz_sobolev_product_bound hs)

lemma sobolevProduct_schwartz {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (f g : 𝓢(E, ℂ)) :
    sobolevProduct hs (schwartzToSobolev s f) (schwartzToSobolev s g) =
      schwartzToSobolev s (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) :=
  bilinearExtension_apply _ _ _ _ _ (sobolevAlgebraConstant_nonneg s) f g

lemma sobolevProduct_bound {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (u v : FourierSobolevSpace E ℂ s) :
    ‖sobolevProduct hs u v‖ ≤ sobolevAlgebraConstant (E := E) s * ‖u‖ * ‖v‖ :=
  bilinearExtension_bound _ _ _ _ _ (sobolevAlgebraConstant_nonneg s) u v

def inverseBesselLp {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    Lp ℂ 2 (volume : Measure E) :=
  (memLp_bessel_weight hs).ofReal.toLp
    (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2)))

def sobolevFourierL1 {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    FourierSobolevSpace E ℂ s →L[ℂ] Lp ℂ 1 (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := fun u => (inverseBesselLp hs • u : Lp ℂ 1 (volume : Measure E))
      map_add' := fun u v => Lp.add_smul (r := 1) (inverseBesselLp hs) u v
      map_smul' := fun c u => (Lp.smul_comm (r := 1) c (inverseBesselLp hs) u).symm }
    ‖inverseBesselLp hs‖
    (fun u => Lp.norm_smul_le (r := 1) (inverseBesselLp hs) u)

def sobolevRepresentative {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    FourierSobolevSpace E ℂ s →L[ℂ] E →ᵇ ℂ :=
  Real.Lp.fourierTransformInvCLM E ℂ ∘L sobolevFourierL1 hs

lemma sobolevRepresentative_distribution {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s) (u : FourierSobolevSpace E ℂ s) :
    boundedDistribution (sobolevRepresentative hs u) = fourierSobolevDistribution E ℂ s u := by
  change boundedDistribution (inverseFourierL1 (inverseBesselLp hs • u)) = _
  rw [inverseFourierL1_distribution, inverseBesselLp,
    Lp.toTemperedDistribution_smul_eq (by fun_prop)]
  rfl

lemma boundedDistribution_schwartz (f : 𝓢(E, ℂ)) :
    boundedDistribution f.toBoundedContinuousFunction = (f : 𝓢'(E, ℂ)) := by
  ext φ
  rw [boundedDistribution_apply, SchwartzMap.coe_apply]
  rfl

lemma sobolevRepresentative_schwartz {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (f : 𝓢(E, ℂ)) :
    sobolevRepresentative hs (schwartzToSobolev s f) = f.toBoundedContinuousFunction := by
  apply boundedDistribution_injective
  rw [sobolevRepresentative_distribution, schwartzToSobolev_distribution,
    boundedDistribution_schwartz]

theorem sobolevRepresentative_product {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (u v : FourierSobolevSpace E ℂ s) :
    sobolevRepresentative hs (sobolevProduct hs u v) =
      sobolevRepresentative hs u * sobolevRepresentative hs v := by
  refine (denseRange_schwartzToSobolev (E := E) s).induction_on₂ ?_ ?_ u v
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro f g
    rw [sobolevProduct_schwartz, sobolevRepresentative_schwartz,
      sobolevRepresentative_schwartz, sobolevRepresentative_schwartz]
    ext x
    simp [SchwartzMap.pairing_apply_apply]

end YauCounterexamples

end

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
namespace YauCounterexamples
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def momentBesselLp {s : ℝ} (n : ℕ) (hs : Module.finrank ℝ E < 2 * (s - n)) :
    Lp ℂ 2 (volume : Measure E) :=
  (memLp_moment_bessel_weight n hs).ofReal.toLp
    (fun x : E => Complex.ofReal (‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2)))

lemma fourierL1_moment_norm {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (n : ℕ) (hn : Module.finrank ℝ E < 2 * (s - n))
    (u : FourierSobolevSpace E ℂ s) :
    Integrable (fun x : E => ‖x‖ ^ n * ‖sobolevFourierL1 hs u x‖) ∧
      (∫ x : E, ‖x‖ ^ n * ‖sobolevFourierL1 hs u x‖) ≤ ‖momentBesselLp n hn‖ * ‖u‖ := by
  let v : Lp ℂ 1 (volume : Measure E) := momentBesselLp n hn • u
  have he : (fun x : E => ‖v x‖) =ᵐ[volume]
      (fun x : E => ‖x‖ ^ n * ‖sobolevFourierL1 hs u x‖) := by
    have hw := ((memLp_bessel_weight hs).ofReal :
      MemLp (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) 2).coeFn_toLp
    have hm := ((memLp_moment_bessel_weight n hn).ofReal :
      MemLp (fun x : E => Complex.ofReal (‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2))) 2).coeFn_toLp
    filter_upwards [Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) (momentBesselLp n hn) u,
      Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) (inverseBesselLp hs) u, hw, hm] with x hx hy hw hm
    change ‖(momentBesselLp n hn • u : Lp ℂ 1 volume) x‖ = _
    rw [hx]
    change ‖(momentBesselLp n hn : E → ℂ) x • u x‖ =
      ‖x‖ ^ n * ‖(inverseBesselLp hs • u : Lp ℂ 1 volume) x‖
    rw [hy]
    change ‖((memLp_moment_bessel_weight n hn).ofReal.toLp _ : E → ℂ) x • u x‖ =
      ‖x‖ ^ n * ‖((memLp_bessel_weight hs).ofReal.toLp _ : E → ℂ) x • u x‖
    erw [hm, hw]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2)),
      abs_of_nonneg (by positivity : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-s / 2))]
    ring
  refine ⟨(memLp_one_iff_integrable.mp (Lp.memLp v)).norm.congr he, ?_⟩
  calc
    _ = ∫ x : E, ‖v x‖ := integral_congr_ae he.symm
    _ = ‖v‖ := (L1.norm_eq_integral_norm v).symm
    _ ≤ _ := Lp.norm_smul_le (momentBesselLp n hn) u

theorem sobolevRepresentative_jet_bound {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (n : ℕ) (hn : Module.finrank ℝ E < 2 * (s - n))
    (u : FourierSobolevSpace E ℂ s) (x : E) :
    ‖iteratedFDeriv ℝ n (sobolevRepresentative hs u : E → ℂ) x‖ ≤
      (2 * Real.pi * ‖innerSL ℝ (E := E)‖) ^ n * ‖momentBesselLp n hn‖ * ‖u‖ := by
  let v := sobolevFourierL1 hs u
  have hm (j : ℕ) (hj : j ≤ n) : Integrable (fun y : E => ‖y‖ ^ j * ‖v y‖) := by
    apply (fourierL1_moment_norm hs j _ u).1
    have : (j : ℝ) ≤ n := by exact_mod_cast hj
    linarith
  have hf : iteratedFDeriv ℝ n (𝓕 (v : E → ℂ)) =
      𝓕 (fun y => VectorFourier.fourierPowSMulRight (innerSL ℝ) (v : E → ℂ) y n) :=
    Real.iteratedFDeriv_fourier (N := (n : ℕ∞))
      (fun j hj => hm j (by exact_mod_cast hj)) (Lp.aestronglyMeasurable v) le_rfl
  have hneg : (sobolevRepresentative hs u : E → ℂ) =
      (𝓕 (v : E → ℂ)) ∘ (LinearIsometryEquiv.neg ℝ (E := E)) := by
    ext y
    rfl
  rw [hneg, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right, hf]
  have hi := VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ) (hm n le_rfl)
    (Lp.aestronglyMeasurable v)
  calc
    _ ≤ ∫ y : E, ‖VectorFourier.fourierPowSMulRight (innerSL ℝ) (v : E → ℂ) y n‖ := by
      rw [Real.fourier_eq]
      apply (norm_integral_le_integral_norm _).trans_eq
      simp only [Circle.norm_smul]
    _ ≤ ∫ y : E, (2 * Real.pi * ‖innerSL ℝ (E := E)‖) ^ n * (‖y‖ ^ n * ‖v y‖) := by
      apply integral_mono hi.norm ((hm n le_rfl).const_mul _)
      intro y
      exact (VectorFourier.norm_fourierPowSMulRight_le _ _ y n).trans_eq (by ring)
    _ = (2 * Real.pi * ‖innerSL ℝ (E := E)‖) ^ n * ∫ y : E, ‖y‖ ^ n * ‖v y‖ := integral_const_mul _ _
    _ ≤ (2 * Real.pi * ‖innerSL ℝ (E := E)‖) ^ n * (‖momentBesselLp n hn‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (fourierL1_moment_norm hs n hn u).2
        (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)
          (innerSL ℝ (E := E)).opNorm_nonneg) n)
    _ = _ := by ring

end YauCounterexamples

end

end OAI
