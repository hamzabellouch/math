import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingEstimates
import OAI.Analysis.IrrationalRotation.Analysis.BanachPeriodicIntervalDiscrepancy

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem eVariationOn_ofReal (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => (f x : ℂ)) s = eVariationOn f s := by
  simp only [eVariationOn, Complex.isometry_ofReal.edist_eq]

theorem bvSize_ofReal_le (f : ℝ → ℝ)
    (hf : BddAbove (Set.range (fun x => |f x|))) :
    bvSize (fun x => (f x : ℂ)) ≤
      sSup (Set.range (fun x => |f x|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal := by
  rw [bvSize, eVariationOn_ofReal]
  apply add_le_add _ le_rfl
  apply csSup_le (Set.Nonempty.image _ (nonempty_Icc.mpr (by norm_num)))
  rintro _ ⟨x, _, rfl⟩
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    (le_csSup hf (show |f x| ∈ Set.range (fun x => |f x|) from ⟨x, rfl⟩))

theorem manuscript_kernel_abs_le {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) (s v : ℝ) :
    |u s v| ≤ (m : ℝ)^(13 / 5 : ℝ) := by
  have hfirst (z : ℝ) : |manuscriptKernel m z v| ≤ (m : ℝ)^(13 / 5 : ℝ) := by
    have hn : 0 ≤ manuscriptKernel m z v :=
      rawKernel_nonneg (manuscript_parameters hm).1.le
        ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩
    rw [abs_of_nonneg hn]
    exact manuscriptKernel_le_height hm z v
  rcases hu with rfl | rfl
  · exact hfirst s
  · exact hfirst (s - v)

theorem manuscript_kernel_nonneg {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) (s v : ℝ) :
    0 ≤ u s v := by
  rcases hu with rfl | rfl <;>
    exact rawKernel_nonneg (manuscript_parameters hm).1.le
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

theorem manuscript_kernel_measurable {m : ℕ} {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    Measurable (Function.uncurry u) := by
  rcases hu with rfl | rfl
  · exact measurable_circleKernel _ _
  · exact measurable_circleEndpoint_pair _ _

theorem manuscript_kernel_intervalIntegrable {m : ℕ} (hm : 200 ≤ m)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (s : ℝ) : IntervalIntegrable (u s) volume 0 1 := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound
    (by rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
    ((manuscript_kernel_measurable hu).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    ((m : ℝ)^(13 / 5 : ℝ))
  exact Filter.Eventually.of_forall fun v => by
    change ‖u s v‖ ≤ _
    simpa only [Real.norm_eq_abs] using manuscript_kernel_abs_le hm hu s v

theorem manuscript_kernel_square_intervalIntegrable {m : ℕ} (hm : 200 ≤ m)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (s : ℝ) : IntervalIntegrable (fun v => (u s v)^2) volume 0 1 := by
  apply intervalIntegrable_square_of_bound
    (manuscript_kernel_intervalIntegrable hm hu s).def'.aestronglyMeasurable
    (by positivity : 0 ≤ (m : ℝ)^(13 / 5 : ℝ))
  intro v _
  exact manuscript_kernel_abs_le hm hu s v

theorem one_power_kernel_cross_error {m : ℕ} (hm : 200 ≤ m) {N₀ n : ℝ}
    (hN : 0 < N₀) (hn : 0 < n)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (s : ℝ) :
    |(∫ x, u s (Int.fract (n * x)) * (∫ v in (0 : ℝ)..1, u s v)
        ∂UniformIntervalPhase.lambdaLaw N₀) - (∫ v in (0 : ℝ)..1, u s v)^2| ≤
      4 * (N₀ / n) := by
  have h := PeriodicIntervalDiscrepancy.uniform_angle_test_le hN hn
    (manuscript_kernel_intervalIntegrable hm hu s)
  rw [← UniformIntervalPhase.lambdaLaw_eq_cond N₀ hN] at h
  have habs : (fun v => |u s v|) = u s :=
    funext fun v => abs_of_nonneg (manuscript_kernel_nonneg hm hu s v)
  rw [habs] at h
  obtain ⟨hb0, hb2⟩ := (both_kernel_estimates hm hu).average_bounds s
  let b := ∫ v in (0 : ℝ)..1, u s v
  change |(∫ x, u s (Int.fract (n * x)) * b ∂UniformIntervalPhase.lambdaLaw N₀) - b^2| ≤ _
  rw [integral_mul_const]
  have heq (a : ℝ) : a * b - b^2 = (a - b) * b := by ring
  rw [heq, abs_mul, abs_of_nonneg hb0]
  calc
    _ ≤ ((N₀ / n) * b) * b := mul_le_mul_of_nonneg_right h hb0
    _ = (N₀ / n) * b^2 := by ring
    _ ≤ (N₀ / n) * 4 := mul_le_mul_of_nonneg_left (by dsimp [b]; nlinarith) (by positivity)
    _ = _ := by ring

theorem one_power_kernel_square_le {m : ℕ} (hm : 200 ≤ m) {N₀ n : ℝ}
    (hN : 0 < N₀) (hn : N₀ ≤ n)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (s : ℝ) :
    (∫ x, (u s (Int.fract (n * x)))^2 ∂UniformIntervalPhase.lambdaLaw N₀) ≤
      2 * ∫ v in (0 : ℝ)..1, (u s v)^2 := by
  have hn0 := hN.trans_le hn
  have h := PeriodicIntervalDiscrepancy.uniform_angle_test_le hN hn0
    (manuscript_kernel_square_intervalIntegrable hm hu s)
  rw [← UniformIntervalPhase.lambdaLaw_eq_cond N₀ hN] at h
  simp only [abs_sq] at h
  have hr : N₀ / n ≤ 1 := (div_le_one hn0).mpr hn
  have hb : 0 ≤ ∫ v in (0 : ℝ)..1, (u s v)^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  have hh := (abs_le.mp h).2
  nlinarith [mul_le_mul_of_nonneg_right hr hb]

theorem manuscript_kernel_complex_bv {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) (s : ℝ) :
    BoundedVariationOn (fun v => (u s v : ℂ)) (Icc (0 : ℝ) 1) ∧
      0 ≤ bvSize (fun v => (u s v : ℂ)) ∧
      bvSize (fun v => (u s v : ℂ)) ≤ 11 * (m : ℝ)^10 := by
  have hk := both_kernel_estimates hm hu
  have hb : BddAbove (Set.range (fun v => |u s v|)) := by
    refine ⟨(m : ℝ)^(13 / 5 : ℝ), ?_⟩
    rintro _ ⟨v, rfl⟩
    exact manuscript_kernel_abs_le hm hu s v
  have hb' : BddAbove ((fun v => ‖(u s v : ℂ)‖) '' Icc (0 : ℝ) 1) := by
    refine ⟨(m : ℝ)^(13 / 5 : ℝ), ?_⟩
    rintro _ ⟨v, _, rfl⟩
    simpa only [Complex.norm_real, Real.norm_eq_abs] using manuscript_kernel_abs_le hm hu s v
  refine ⟨?_, ?_, (bvSize_ofReal_le (u s) hb).trans (hk.variation_coarse s)⟩
  · unfold BoundedVariationOn
    rw [eVariationOn_ofReal]
    exact hk.boundedVariation s
  · unfold bvSize
    apply add_nonneg _ ENNReal.toReal_nonneg
    exact (norm_nonneg (u s 0 : ℂ)).trans (le_csSup hb' ⟨0, by norm_num, rfl⟩)

theorem two_power_kernel_error {m : ℕ} (hm : 200 ≤ m) {N₀ C : ℝ}
    {n n' : ℕ} (hC : 0 ≤ C) (hBV : BVEstimate m N₀ n n' C)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (s : ℝ) :
    |(∫ x, u s (Int.fract ((n : ℝ) * x)) * u s (Int.fract ((n' : ℝ) * x))
        ∂UniformIntervalPhase.lambdaLaw N₀) - (∫ v in (0 : ℝ)..1, u s v)^2| ≤
      121 * C * (m : ℝ)^(-(60 : ℝ)) := by
  obtain ⟨hbv, hnonneg, hbound⟩ := manuscript_kernel_complex_bv hm hu s
  have h := hBV (fun v => (u s v : ℂ)) (fun v => (u s v : ℂ)) hbv hbv
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, intervalIntegral.integral_ofReal,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  rw [← sq] at h
  refine h.trans ?_
  have hp : 0 ≤ C * (m : ℝ)^(-(80 : ℝ)) := by positivity
  calc
    C * (m : ℝ)^(-(80 : ℝ)) * bvSize (fun v => (u s v : ℂ)) *
        bvSize (fun v => (u s v : ℂ)) ≤
      C * (m : ℝ)^(-(80 : ℝ)) * (11 * (m : ℝ)^10) * (11 * (m : ℝ)^10) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hbound hp) hbound hnonneg
        (mul_nonneg hp (by positivity))
    _ = 121 * C * (m : ℝ)^(-(60 : ℝ)) := by
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      norm_num [Real.rpow_neg, Real.rpow_natCast]
      field_simp
      ring

end Invariant233.ScalarSampling

end

end OAI
