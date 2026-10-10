import OAI.MathematicalPhysics.Boltzmann.Collision.AxialFlow
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityWeight

namespace OAI

section

/-!
# Uniform transverse disk bounds

This proves the translated disk estimate `ker:disk-singularity` from Section 3.
The singular contribution is split at distance `R` from the origin. Inside,
polar integration is explicit; outside, the singularity is at most `R⁻ᑫ`.
-/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.TransverseDisk

def diskConstant (q : ℝ) : ℝ := Real.pi + 2 * Real.pi / (2 - q)

theorem diskConstant_pos {q : ℝ} (hq : q < 2) : 0 < diskConstant q := by
  unfold diskConstant
  positivity

theorem diskConstant_ge_pi {q : ℝ} (hq : q < 2) : Real.pi ≤ diskConstant q := by
  unfold diskConstant
  have hd : 0 ≤ 2 * Real.pi / (2 - q) := by positivity
  linarith

theorem closedDisk_volume_real (a : Transverse) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (closedBall a R) = Real.pi * R ^ 2 := by
  rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hR, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

theorem disk_volume_real (a : Transverse) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (ball a R) = Real.pi * R ^ 2 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hR, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

theorem integrableOn_singularity_closedDisk {q : ℝ} (hq : q < 2)
    (a : Transverse) (R : ℝ) : IntegrableOn (singularity q) (closedBall a R) :=
  (locallyIntegrable_singularity hq).integrableOn_isCompact (isCompact_closedBall a R)

theorem integrableOn_singularity_disk {q : ℝ} (hq : q < 2)
    (a : Transverse) (R : ℝ) : IntegrableOn (singularity q) (ball a R) :=
  (integrableOn_singularity_closedDisk hq a R).mono_set ball_subset_closedBall

/-- Exact centered disk integral, including the integrable singularity at the origin. -/
theorem integral_singularity_centeredDisk {q R : ℝ} (hq : q < 2) (hR : 0 < R) :
    (∫ u in ball (0 : Transverse) R, singularity q u) =
      2 * Real.pi / (2 - q) * R ^ (2 - q) := by
  have hcut : (ball (0 : Transverse) R).indicator (singularity q) =
      fun u : Transverse => (Iio R).indicator (fun r : ℝ => r ^ (-q)) ‖u‖ := by
    funext u
    by_cases hu : ‖u‖ < R <;> simp [indicator, singularity, hu]
  rw [← integral_indicator measurableSet_ball, hcut,
    integral_fun_norm_addHaar (volume : Measure Transverse)]
  have hrad : (∫ r in Ioi (0 : ℝ),
      r ^ (Module.finrank ℝ Transverse - 1) •
        (Iio R).indicator (fun t : ℝ => t ^ (-q)) r) =
      ∫ r in Ioo (0 : ℝ) R, r ^ (1 - q) := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), (Iio R).indicator (fun t : ℝ => t ^ (1 - q)) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have hr₀ : 0 < r := hr
        by_cases hrR : r < R
        · simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
            pow_one, smul_eq_mul, indicator_of_mem (show r ∈ Iio R from hrR)]
          rw [show 1 - q = 1 + -q by ring, Real.rpow_add hr₀, Real.rpow_one]
        · simp [hrR]
      _ = _ := by
        rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          inter_comm, Ioi_inter_Iio]
  rw [hrad, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
    integral_rpow (Or.inl (by linarith : -1 < 1 - q))]
  have hz : (0 : ℝ) ^ ((1 - q) + 1) = 0 := Real.zero_rpow (by linarith)
  rw [hz, sub_zero, disk_volume_real 0 (by norm_num)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  rw [show (1 - q) + 1 = 2 - q by ring]
  ring

private theorem singularity_split_bound {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (u : Transverse) :
    singularity q u ≤ (ball (0 : Transverse) R).indicator (singularity q) u + R ^ (-q) := by
  by_cases hu : u ∈ ball (0 : Transverse) R
  · rw [indicator_of_mem hu]
    have hn : 0 ≤ R ^ (-q) := Real.rpow_nonneg hR.le _
    linarith
  · rw [indicator_of_notMem hu, zero_add]
    have hnorm : R ≤ ‖u‖ := le_of_not_gt (by simpa only [mem_ball_zero_iff] using hu)
    exact Real.rpow_le_rpow_of_nonpos hR hnorm (neg_nonpos.mpr hq)

private theorem radius_pow_mul {R q : ℝ} (hR : 0 < R) :
    R ^ 2 * R ^ (-q) = R ^ (2 - q) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hR]
  congr 1

theorem integral_singularity_closedDisk_le {q R : ℝ} (hq₀ : 0 ≤ q) (hq₂ : q < 2)
    (hR : 0 < R) (a : Transverse) :
    (∫ u in closedBall a R, singularity q u) ≤ diskConstant q * R ^ (2 - q) := by
  let near : Transverse → ℝ := (ball (0 : Transverse) R).indicator (singularity q)
  have hn : Integrable near :=
    (integrableOn_singularity_disk hq₂ 0 R).integrable_indicator measurableSet_ball
  have hc : IntegrableOn (fun _ : Transverse => R ^ (-q)) (closedBall a R) :=
    integrableOn_const measure_closedBall_lt_top.ne
  have hnear : 0 ≤ᵐ[volume] near := ae_of_all _ (fun u =>
    indicator_nonneg (fun u _ => singularity_nonneg q u) u)
  calc
    _ ≤ ∫ u in closedBall a R, near u + R ^ (-q) :=
      setIntegral_mono_on (integrableOn_singularity_closedDisk hq₂ a R)
        (hn.integrableOn.add hc) measurableSet_closedBall
        (fun u _ => singularity_split_bound hq₀ hR u)
    _ = (∫ u in closedBall a R, near u) +
        volume.real (closedBall a R) * R ^ (-q) := by
      rw [integral_add hn.integrableOn hc, setIntegral_const, smul_eq_mul]
    _ ≤ (∫ u, near u) + volume.real (closedBall a R) * R ^ (-q) := by
      have h := setIntegral_le_integral (s := closedBall a R) hn hnear
      linarith
    _ = _ := by
      rw [show (∫ u, near u) = ∫ u in ball (0 : Transverse) R, singularity q u from
        integral_indicator measurableSet_ball,
        integral_singularity_centeredDisk hq₂ hR, closedDisk_volume_real a hR.le]
      unfold diskConstant
      rw [mul_assoc Real.pi, radius_pow_mul hR]
      ring

theorem integrableOn_diskWeight_closedDisk {q : ℝ} (hq : q < 2)
    (a : Transverse) (R : ℝ) :
    IntegrableOn (fun u => 1 + singularity q u) (closedBall a R) := by
  have hc : IntegrableOn (fun _ : Transverse => (1 : ℝ)) (closedBall a R) :=
    integrableOn_const measure_closedBall_lt_top.ne
  exact hc.add (integrableOn_singularity_closedDisk hq a R)

/-- The uniform translated closed-disk bound from `ker:disk-singularity`. -/
theorem integral_diskWeight_closedDisk_le {q R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hR : 0 < R) (a : Transverse) :
    (∫ u in closedBall a R, 1 + singularity q u) ≤
      diskConstant q * (R ^ 2 + R ^ (2 - q)) := by
  have hq₀ : 0 ≤ q := by linarith
  have hc : IntegrableOn (fun _ : Transverse => (1 : ℝ)) (closedBall a R) :=
    integrableOn_const measure_closedBall_lt_top.ne
  calc
    _ = Real.pi * R ^ 2 + ∫ u in closedBall a R, singularity q u := by
      rw [integral_add hc (integrableOn_singularity_closedDisk hq₂ a R),
        setIntegral_const, smul_eq_mul, mul_one, closedDisk_volume_real a hR.le]
    _ ≤ Real.pi * R ^ 2 + diskConstant q * R ^ (2 - q) := by
      have h := integral_singularity_closedDisk_le hq₀ hq₂ hR a
      linarith
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (diskConstant_ge_pi hq₂) (sq_nonneg R)
      nlinarith

theorem integrableOn_diskWeight_disk {q : ℝ} (hq : q < 2)
    (a : Transverse) (R : ℝ) : IntegrableOn (fun u => 1 + singularity q u) (ball a R) :=
  (integrableOn_diskWeight_closedDisk hq a R).mono_set ball_subset_closedBall

theorem integral_diskWeight_disk_le {q R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hR : 0 < R) (a : Transverse) :
    (∫ u in ball a R, 1 + singularity q u) ≤
      diskConstant q * (R ^ 2 + R ^ (2 - q)) := by
  apply (setIntegral_mono_set (integrableOn_diskWeight_closedDisk hq₂ a R)
    (ae_of_all _ (fun u => add_nonneg zero_le_one (singularity_nonneg q u)))
    (ae_of_all _ (fun _ h => ball_subset_closedBall h))).trans
  exact integral_diskWeight_closedDisk_le hq₁ hq₂ hR a

end BoltzmannNonuniqueness.TransverseDisk

end

end

section

/-!
# Transverse collision-line coordinates

An orthonormal line chart gives the regular and singular terms in the
geometric slice estimate of Section 3. The singular distance is assumed
nonzero here; the product-measure argument must remove its null exceptional set.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.AxialSlices

namespace BoltzmannNonuniqueness.TransverseLine

def quarterTurn (e : Transverse) : Transverse := WithLp.toLp 2 ![-e 1, e 0]

def line (e : Transverse) (D s : ℝ) : Transverse := D • e + s • quarterTurn e

theorem inner_quarterTurn (e : Transverse) : inner ℝ e (quarterTurn e) = 0 := by
  simp [PiLp.inner_apply, quarterTurn, Fin.sum_univ_two]
  ring

theorem norm_quarterTurn (e : Transverse) : ‖quarterTurn e‖ = ‖e‖ := by
  have h : ‖quarterTurn e‖ ^ 2 = ‖e‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, quarterTurn, Fin.sum_univ_two]
    ring
  nlinarith [norm_nonneg e, norm_nonneg (quarterTurn e)]

theorem norm_line_sq (e : Transverse) (D s : ℝ) (he : ‖e‖ = 1) :
    ‖line e D s‖ ^ 2 = D ^ 2 + s ^ 2 := by
  have hnorm : e 0 ^ 2 + e 1 ^ 2 = 1 := by
    have hsq : ‖e‖ ^ (2 : ℕ) = 1 := by rw [he]; norm_num
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] at hsq
    exact hsq
  calc
    _ = (D ^ 2 + s ^ 2) * (e 0 ^ 2 + e 1 ^ 2) := by
      simp [line, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, quarterTurn]
      ring
    _ = _ := by rw [hnorm, mul_one]

theorem inner_line (e : Transverse) (D s : ℝ) (he : ‖e‖ = 1) :
    inner ℝ e (line e D s) = D := by
  simp only [line, inner_add_right, inner_smul_right, inner_quarterTurn,
    real_inner_self_eq_norm_sq, he]
  ring

theorem inner_quarterTurn_line (e : Transverse) (D s : ℝ) (he : ‖e‖ = 1) :
    inner ℝ (quarterTurn e) (line e D s) = s := by
  have hp : inner ℝ (quarterTurn e) e = 0 := by
    rw [real_inner_comm, inner_quarterTurn]
  simp only [line, inner_add_right, inner_smul_right, hp,
    real_inner_self_eq_norm_sq, norm_quarterTurn, he]
  ring

/-- The normal and tangential coordinates recover every transverse vector. -/
theorem line_reconstruct (e u : Transverse) (he : ‖e‖ = 1) :
    line e (inner ℝ e u) (inner ℝ (quarterTurn e) u) = u := by
  have hnorm : e 0 ^ 2 + e 1 ^ 2 = 1 := by
    have hsq : ‖e‖ ^ (2 : ℕ) = 1 := by rw [he]; norm_num
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] at hsq
    exact hsq
  apply (WithLp.ext_iff 2).mpr
  funext i
  fin_cases i
  · simp [line, quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination u 0 * hnorm
  · simp [line, quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination u 1 * hnorm

theorem line_singularity (q : ℝ) (e : Transverse) (D s : ℝ) (he : ‖e‖ = 1) :
    ‖line e D s‖ ^ (-q) = (D ^ 2 + s ^ 2) ^ (-q / 2) := by
  rw [← norm_line_sq e D s he, ← Real.rpow_natCast_mul (norm_nonneg _) 2]
  congr 1
  ring

def lineWeight (q : ℝ) (e : Transverse) (D s : ℝ) : ℝ :=
  1 + ‖line e D s‖ ^ (-q)

theorem lineWeight_nonneg (q : ℝ) (e : Transverse) (D s : ℝ) :
    0 ≤ lineWeight q e D s := by
  unfold lineWeight
  positivity

theorem integrable_line_singularity {q D : ℝ} (hq : 1 < q) (hD : D ≠ 0)
    (e : Transverse) (he : ‖e‖ = 1) :
    Integrable (fun s : ℝ => ‖line e D s‖ ^ (-q)) := by
  simpa only [line_singularity q e D _ he] using integrable_singular_line hq hD

theorem integrableOn_lineWeight {q D : ℝ} (hq : 1 < q) (hD : D ≠ 0)
    (e : Transverse) (he : ‖e‖ = 1) (m R : ℝ) :
    IntegrableOn (lineWeight q e D) (Icc (m - R) (m + R)) := by
  exact (integrableOn_const (measure_Icc_lt_top.ne)).add
    (integrable_line_singularity hq hD e he).integrableOn

/-- The line bound is uniform in the center of the retained segment. -/
theorem integral_lineWeight_le {q D R : ℝ} (hq : 1 < q) (hD : D ≠ 0)
    (hR : 0 ≤ R) (e : Transverse) (he : ‖e‖ = 1) (m : ℝ) :
    (∫ s in Icc (m - R) (m + R), lineWeight q e D s) ≤
      2 * R + lineConstant q * |D| ^ (1 - q) := by
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (m - R) (m + R)) :=
    integrableOn_const measure_Icc_lt_top.ne
  have hs := integrable_line_singularity hq hD e he
  have hb := setIntegral_le_integral (s := Icc (m - R) (m + R)) hs
    (Filter.Eventually.of_forall (fun s => Real.rpow_nonneg (norm_nonneg (line e D s)) (-q)))
  unfold lineWeight
  rw [integral_add hc hs.integrableOn, setIntegral_const, smul_eq_mul, mul_one]
  have hvol : volume.real (Icc (m - R) (m + R)) = 2 * R := by
    rw [Real.volume_real_Icc]
    rw [max_eq_left (by linarith : 0 ≤ m + R - (m - R))]
    ring
  rw [hvol]
  have hfull : (∫ s : ℝ, ‖line e D s‖ ^ (-q)) = lineConstant q * |D| ^ (1 - q) := by
    simp_rw [line_singularity q e D _ he]
    exact (singular_line_formula hq hD).2
  linarith

theorem lintegral_lineWeight_le {q D R : ℝ} (hq : 1 < q) (hD : D ≠ 0)
    (hR : 0 ≤ R) (e : Transverse) (he : ‖e‖ = 1) (m : ℝ) :
    (∫⁻ s in Icc (m - R) (m + R), ENNReal.ofReal (lineWeight q e D s)) ≤
      ENNReal.ofReal (2 * R + lineConstant q * |D| ^ (1 - q)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_lineWeight hq hD e he m R)
    (Filter.Eventually.of_forall (fun s => lineWeight_nonneg q e D s))]
  exact ENNReal.ofReal_le_ofReal (integral_lineWeight_le hq hD hR e he m)

end BoltzmannNonuniqueness.TransverseLine

end

end

section

/-!
# Transverse angular averages

The angular singularity in `ker:transverse-expectation` is integrable when
`q < 2`. Gaussian Cartesian integration and polar coordinates prove this
without choosing a trigonometric chart on the unit circle.
-/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.TransverseAverage

abbrev Circle := sphere (0 : Transverse) 1

def circleArea : Measure Circle := (volume : Measure Transverse).toSphere

instance circleArea_isFiniteMeasure : IsFiniteMeasure circleArea := by
  unfold circleArea
  infer_instance

def unitAxis : Transverse := EuclideanSpace.single 0 1

theorem norm_unitAxis : ‖unitAxis‖ = 1 := by
  simp [unitAxis, EuclideanSpace.single, PiLp.norm_single]

def angular (q : ℝ) (e : Transverse) (ω : Circle) : ℝ :=
  |inner ℝ e (ω : Transverse)| ^ (1 - q)

def gaussianPower (q : ℝ) (e x : Transverse) : ℝ :=
  |inner ℝ e x| ^ (1 - q) * Real.exp (-‖x‖ ^ 2)

def radialGaussian (q : ℝ) (r : Ioi (0 : ℝ)) : ℝ :=
  (r : ℝ) ^ (1 - q) * Real.exp (-(r : ℝ) ^ 2)

private theorem radialMeasure_ne_zero : Measure.volumeIoiPow 1 ≠ 0 := by
  intro hz
  have h := Measure.volumeIoiPow_apply_Iio 1 (⟨1, by norm_num⟩ : Ioi (0 : ℝ))
  rw [hz] at h
  norm_num at h

private instance radialMeasure_neZero : NeZero (Measure.volumeIoiPow 1) :=
  ⟨radialMeasure_ne_zero⟩

theorem circleArea_real_univ : circleArea.real univ = 2 * Real.pi := by
  rw [circleArea, Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_two]
  norm_num [ENNReal.toReal_ofReal, Real.pi_pos.le]

private theorem integrable_abs_rpow_gaussian {q : ℝ} (hq : q < 2) :
    Integrable (fun x : ℝ => |x| ^ (1 - q) * Real.exp (-x ^ 2)) := by
  have hr := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) zero_lt_one
    (show -1 < 1 - q by linarith)
  have h := (integrable_fun_norm_addHaar (volume : Measure ℝ)
    (f := fun r : ℝ => r ^ (1 - q) * Real.exp (-r ^ 2))).mpr
      (by simpa using hr)
  simpa only [Real.norm_eq_abs, sq_abs] using h

private def cartesianSplit : Transverse ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

private theorem cartesianSplit_measurePreserving : MeasurePreserving cartesianSplit :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
    (volume_preserving_finTwoArrow ℝ)

private theorem gaussianPower_unitAxis (q : ℝ) (x : Transverse) :
    gaussianPower q unitAxis x = |x 0| ^ (1 - q) * Real.exp (-‖x‖ ^ 2) := by
  simp [gaussianPower, unitAxis, EuclideanSpace.inner_single_left]

theorem integrable_gaussianPower_unitAxis {q : ℝ} (hq : q < 2) :
    Integrable (gaussianPower q unitAxis) := by
  have hi := (integrable_abs_rpow_gaussian hq).mul_prod (integrable_exp_neg_mul_sq zero_lt_one)
  have hc := cartesianSplit_measurePreserving.integrable_comp_of_integrable hi
  convert hc using 1
  funext x
  rw [gaussianPower_unitAxis]
  change |x 0| ^ (1 - q) * Real.exp (-‖x‖ ^ 2) =
    |x 0| ^ (1 - q) * Real.exp (-(x 0) ^ 2) * Real.exp (-1 * (x 1) ^ 2)
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, neg_add_rev,
    Real.exp_add, neg_mul, one_mul]
  ring

private theorem gaussianPower_rotate (e : Transverse) (he : ‖e‖ = 1) :
    ∃ R : Transverse ≃ₗᵢ[ℝ] Transverse,
      ∀ q x, gaussianPower q e (R x) = gaussianPower q unitAxis x := by
  let R : Transverse ≃ₗᵢ[ℝ] Transverse := (ℝ ∙ (e - unitAxis))ᗮ.reflection
  have hnorm : ‖e‖ = ‖unitAxis‖ := he.trans norm_unitAxis.symm
  have hRe : R e = unitAxis := Submodule.reflection_sub hnorm
  refine ⟨R, ?_⟩
  intro q x
  have hi : inner ℝ e (R x) = inner ℝ unitAxis x := by
    have h := R.inner_map_eq_flip e x
    rw [hRe] at h
    exact h.symm
  simp only [gaussianPower, hi, R.norm_map]

theorem integrable_gaussianPower {q : ℝ} (hq : q < 2)
    (e : Transverse) (he : ‖e‖ = 1) : Integrable (gaussianPower q e) := by
  obtain ⟨R, hR⟩ := gaussianPower_rotate e he
  apply (R.measurePreserving.integrable_comp_emb R.toHomeomorph.measurableEmbedding).mp
  change Integrable (fun x => gaussianPower q e (R x))
  simpa only [hR] using integrable_gaussianPower_unitAxis hq

theorem integral_gaussianPower (q : ℝ) (e : Transverse) (he : ‖e‖ = 1) :
    (∫ x, gaussianPower q e x) = ∫ x, gaussianPower q unitAxis x := by
  obtain ⟨R, hR⟩ := gaussianPower_rotate e he
  rw [← R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding]
  simp only [hR]

private theorem gaussianPower_polar (q : ℝ) (e : Transverse)
    (ω : Circle) (r : Ioi (0 : ℝ)) :
    gaussianPower q e ((r : ℝ) • (ω : Transverse)) = angular q e ω * radialGaussian q r := by
  have hω : ‖(ω : Transverse)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  have hr : 0 < (r : ℝ) := r.property
  simp only [gaussianPower, angular, radialGaussian, inner_smul_right, abs_mul,
    abs_of_pos hr, norm_smul, Real.norm_eq_abs, hω, mul_one]
  rw [Real.mul_rpow hr.le (abs_nonneg _)]
  ring

private theorem integrable_polar_gaussianPower {q : ℝ} (hq : q < 2)
    (e : Transverse) (he : ‖e‖ = 1) :
    Integrable (fun p : Circle × Ioi (0 : ℝ) => angular q e p.1 * radialGaussian q p.2)
      (circleArea.prod (Measure.volumeIoiPow 1)) := by
  let H := homeomorphUnitSphereProd Transverse
  have hs : Integrable (fun x : ({0}ᶜ : Set Transverse) => gaussianPower q e x)
      ((volume : Measure Transverse).comap (↑)) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp
      (integrable_gaussianPower hq e he).integrableOn
  have hp := (volume : Measure Transverse).measurePreserving_homeomorphUnitSphereProd
  have hi := (hp.integrable_comp_emb H.measurableEmbedding).mp
    (show Integrable ((fun p => gaussianPower q e ((H.symm p : ({0}ᶜ : Set Transverse)) : Transverse))
      ∘ H) ((volume : Measure Transverse).comap (↑)) by
      simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hs)
  convert hi using 1
  · funext p
    simp only [H, homeomorphUnitSphereProd_symm_apply_coe, gaussianPower_polar]
  · simp only [circleArea, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub]

theorem integrable_angular {q : ℝ} (hq : q < 2)
    (e : Transverse) (he : ‖e‖ = 1) : Integrable (angular q e) circleArea := by
  obtain ⟨r, hr⟩ := (integrable_polar_gaussianPower hq e he).prod_left_ae.exists
  have hc : radialGaussian q r ≠ 0 := by
    unfold radialGaussian
    exact ne_of_gt (mul_pos (Real.rpow_pos_of_pos r.property _) (Real.exp_pos _))
  exact (integrable_mul_const_iff (isUnit_iff_ne_zero.mpr hc) _).mp hr

theorem integrable_radialGaussian {q : ℝ} (hq : q < 2) :
    Integrable (radialGaussian q) (Measure.volumeIoiPow 1) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hi : IntegrableOn (fun r : ℝ => r ^ (2 - q) * Real.exp (-r ^ 2)) (Ioi 0) :=
    by simpa only [neg_mul, one_mul] using
      integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) zero_lt_one (by linarith : -1 < 2 - q)
  have hs := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp hi
  convert hs using 1
  funext r
  simp only [Function.comp_def, radialGaussian, pow_one,
    ENNReal.toReal_ofReal r.property.le, smul_eq_mul]
  rw [show 2 - q = 1 + (1 - q) by ring, Real.rpow_add r.property, Real.rpow_one]
  ring

theorem integral_radialGaussian_pos {q : ℝ} (hq : q < 2) :
    0 < ∫ r, radialGaussian q r ∂Measure.volumeIoiPow 1 := by
  have hp : ∀ r, 0 < radialGaussian q r := by
    intro r
    exact mul_pos (Real.rpow_pos_of_pos r.property _) (Real.exp_pos _)
  apply (integral_pos_iff_support_of_nonneg (fun r => (hp r).le)
    (integrable_radialGaussian hq)).mpr
  have hs : Function.support (radialGaussian q) = univ := by
    apply Set.eq_univ_of_forall
    intro r
    exact ne_of_gt (hp r)
  rw [hs]
  exact Measure.measure_univ_pos.mpr radialMeasure_ne_zero

private theorem gaussian_polar_identity (q : ℝ) (e : Transverse) :
    (∫ x, gaussianPower q e x) = (∫ ω, angular q e ω ∂circleArea) *
      ∫ r, radialGaussian q r ∂Measure.volumeIoiPow 1 := by
  let H := homeomorphUnitSphereProd Transverse
  have hp := (volume : Measure Transverse).measurePreserving_homeomorphUnitSphereProd.integral_comp
    H.measurableEmbedding (fun p => gaussianPower q e (H.symm p))
  calc
    _ = ∫ x : ({0}ᶜ : Set Transverse), gaussianPower q e x
        ∂((volume : Measure Transverse).comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫ p : Circle × Ioi (0 : ℝ), angular q e p.1 * radialGaussian q p.2
        ∂circleArea.prod (Measure.volumeIoiPow 1) := by
      simpa only [circleArea, H, Homeomorph.symm_apply_apply,
        homeomorphUnitSphereProd_symm_apply_coe, gaussianPower_polar,
        finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] using hp
    _ = _ := integral_prod_mul _ _

theorem integral_angular_eq {q : ℝ} (hq : q < 2) (e : Transverse) (he : ‖e‖ = 1) :
    (∫ ω, angular q e ω ∂circleArea) = ∫ ω, angular q unitAxis ω ∂circleArea := by
  apply mul_right_cancel₀ (ne_of_gt (integral_radialGaussian_pos hq))
  rw [← gaussian_polar_identity, ← gaussian_polar_identity, integral_gaussianPower q e he]

/-- A finite constant depending only on `q`, independent of the direction. -/
def angularMass (q : ℝ) : ℝ :=
  2 * Real.pi + ∫ ω, angular q unitAxis ω ∂circleArea

theorem angularMass_pos (q : ℝ) : 0 < angularMass q := by
  have h : 0 ≤ ∫ ω, angular q unitAxis ω ∂circleArea :=
    integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
  unfold angularMass
  linarith [Real.pi_pos]

theorem integral_one_add_angular {q : ℝ} (hq : q < 2)
    (e : Transverse) (he : ‖e‖ = 1) :
    (∫ ω, 1 + angular q e ω ∂circleArea) = angularMass q := by
  rw [integral_add (integrable_const 1) (integrable_angular hq e he), integral_const,
    smul_eq_mul, mul_one, circleArea_real_univ, integral_angular_eq hq e he]
  rfl

/-- The degree `-1` kernel in `ker:transverse-expectation`; its value at zero is zero. -/
def kernel (q : ℝ) (e n : Transverse) : ℝ :=
  (1 + |inner ℝ e (‖n‖⁻¹ • n)| ^ (1 - q)) / ‖n‖

theorem kernel_nonneg (q : ℝ) (e n : Transverse) : 0 ≤ kernel q e n := by
  unfold kernel
  positivity

private theorem kernel_on_ray (q : ℝ) (e : Transverse) (ω : Circle) (r : Ioi (0 : ℝ)) :
    kernel q e ((r : ℝ) • (ω : Transverse)) = (1 + angular q e ω) * (r : ℝ)⁻¹ := by
  have hω : ‖(ω : Transverse)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  have hr : 0 < (r : ℝ) := r.property
  simp [kernel, angular, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hω,
    smul_smul, inv_mul_cancel₀ hr.ne', div_eq_mul_inv]

private def radialCutoff (D : ℝ) (r : Ioi (0 : ℝ)) : ℝ :=
  if (r : ℝ) < D then (r : ℝ)⁻¹ else 0

private theorem radialCutoff_weight (D : ℝ) (r : Ioi (0 : ℝ)) :
    (r : ℝ) * radialCutoff D r = (Iio D).indicator (fun _ : ℝ => (1 : ℝ)) r := by
  have hr₀ : (r : ℝ) ≠ 0 := (show (0 : ℝ) < r from r.property).ne'
  by_cases hr : (r : ℝ) < D <;> simp [radialCutoff, hr, indicator, hr₀]

private theorem integrable_radialCutoff {D : ℝ} (_hD : 0 < D) :
    Integrable (radialCutoff D) (Measure.volumeIoiPow 1) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hi : IntegrableOn ((Iio D).indicator (fun _ : ℝ => (1 : ℝ))) (Ioi 0) := by
    rw [integrableOn_indicator_iff measurableSet_Iio]
    have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 D) :=
      integrableOn_const (by simp)
    rw [inter_comm, Ioi_inter_Iio]
    exact hc
  have hs := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp hi
  convert hs using 1
  funext r
  simp only [pow_one, ENNReal.toReal_ofReal r.property.le, smul_eq_mul,
    radialCutoff_weight, Function.comp_def]

private theorem integral_radialCutoff {D : ℝ} (hD : 0 < D) :
    (∫ r, radialCutoff D r ∂Measure.volumeIoiPow 1) = D := by
  rw [Measure.volumeIoiPow,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [pow_one, smul_eq_mul]
  have heq : (fun r : Ioi (0 : ℝ) => (ENNReal.ofReal (r : ℝ)).toReal * radialCutoff D r) =
      fun r : Ioi (0 : ℝ) => (Iio D).indicator (fun _ : ℝ => (1 : ℝ)) r := by
    funext r
    rw [ENNReal.toReal_ofReal (show (0 : ℝ) ≤ r from le_of_lt r.property), radialCutoff_weight]
  rw [heq]
  rw [integral_subtype_comap measurableSet_Ioi,
    integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    inter_comm, Ioi_inter_Iio, setIntegral_const, smul_eq_mul, mul_one]
  simp [measureReal_def, Real.volume_Ioo, hD.le]

private theorem cutoff_kernel_polar (q D : ℝ) (e : Transverse)
    (ω : Circle) (r : Ioi (0 : ℝ)) :
    (ball (0 : Transverse) D).indicator (kernel q e) ((r : ℝ) • (ω : Transverse)) =
      (1 + angular q e ω) * radialCutoff D r := by
  have hω : ‖(ω : Transverse)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  have hr : 0 < (r : ℝ) := r.property
  by_cases hrD : (r : ℝ) < D
  · rw [indicator_of_mem]
    · simp only [kernel_on_ray, radialCutoff, ite_eq_left hrD]
    · simpa only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hω,
        mul_one] using hrD
  · rw [indicator_of_notMem]
    · simp only [radialCutoff, ite_eq_right hrD, mul_zero]
    · simpa only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hω,
        mul_one] using hrD

theorem integrableOn_kernel_centeredDisk {q D : ℝ} (hq : q < 2) (hD : 0 < D)
    (e : Transverse) (he : ‖e‖ = 1) : IntegrableOn (kernel q e) (ball 0 D) := by
  let H := homeomorphUnitSphereProd Transverse
  have hi := ((integrable_const 1).add (integrable_angular hq e he)).mul_prod
    (integrable_radialCutoff hD)
  have hp : MeasurePreserving H ((volume : Measure Transverse).comap (↑))
      (circleArea.prod (Measure.volumeIoiPow 1)) := by
    simpa only [circleArea, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] using
      (volume : Measure Transverse).measurePreserving_homeomorphUnitSphereProd
  have hs := hp.integrable_comp_of_integrable hi
  have hsub : Integrable (fun x : ({0}ᶜ : Set Transverse) =>
      (ball (0 : Transverse) D).indicator (kernel q e) x)
      ((volume : Measure Transverse).comap (↑)) := by
    convert hs using 1
    funext x
    have h := cutoff_kernel_polar q D e (H x).1 (H x).2
    simpa only [H, ← homeomorphUnitSphereProd_symm_apply_coe,
      Homeomorph.symm_apply_apply, Function.comp_def, Pi.add_apply] using h
  have hfull : Integrable ((ball (0 : Transverse) D).indicator (kernel q e)) := by
    have h : IntegrableOn ((ball (0 : Transverse) D).indicator (kernel q e)) {0}ᶜ := by
      apply (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mpr
      exact hsub
    simpa only [IntegrableOn, restrict_compl_singleton] using h
  exact (integrable_indicator_iff measurableSet_ball).mp hfull

/-- The radial Jacobian exactly cancels the inverse-distance factor. -/
theorem integral_kernel_centeredDisk {q D : ℝ} (hq : q < 2) (hD : 0 < D)
    (e : Transverse) (he : ‖e‖ = 1) :
    (∫ n in ball (0 : Transverse) D, kernel q e n) = D * angularMass q := by
  let H := homeomorphUnitSphereProd Transverse
  let f := (ball (0 : Transverse) D).indicator (kernel q e)
  have hp := (volume : Measure Transverse).measurePreserving_homeomorphUnitSphereProd.integral_comp
    H.measurableEmbedding (fun p => f (H.symm p))
  calc
    _ = ∫ n, f n := (integral_indicator measurableSet_ball).symm
    _ = ∫ x : ({0}ᶜ : Set Transverse), f x ∂((volume : Measure Transverse).comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫ p : Circle × Ioi (0 : ℝ), (1 + angular q e p.1) * radialCutoff D p.2
        ∂circleArea.prod (Measure.volumeIoiPow 1) := by
      simpa only [f, circleArea, H, Homeomorph.symm_apply_apply,
        homeomorphUnitSphereProd_symm_apply_coe, cutoff_kernel_polar,
        finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] using hp
    _ = (∫ ω, 1 + angular q e ω ∂circleArea) *
        ∫ r, radialCutoff D r ∂Measure.volumeIoiPow 1 :=
      integral_prod_mul (fun ω : Circle => 1 + angular q e ω) (radialCutoff D)
    _ = _ := by rw [integral_one_add_angular hq e he, integral_radialCutoff hD]; ring

private theorem translated_cutoff_eq {d : ℝ} (_hd : 0 < d) (q : ℝ)
    (e v p : Transverse) (hp : p ∈ ball (0 : Transverse) d) :
    (ball (0 : Transverse) (‖v‖ + d)).indicator (kernel q e) (v - p) = kernel q e (v - p) := by
  apply indicator_of_mem
  rw [mem_ball_zero_iff]
  have hp' : ‖p‖ < d := mem_ball_zero_iff.mp hp
  exact (norm_sub_le v p).trans_lt (by linarith)

theorem integrableOn_kernel_translatedDisk {q d : ℝ} (hq : q < 2) (hd : 0 < d)
    (e : Transverse) (he : ‖e‖ = 1) (v : Transverse) :
    IntegrableOn (fun p => kernel q e (v - p)) (ball (0 : Transverse) d) := by
  have hD : 0 < ‖v‖ + d := by positivity
  have hi := (integrableOn_kernel_centeredDisk hq hD e he).integrable_indicator measurableSet_ball
  have hs := ((volume : Measure Transverse).measurePreserving_sub_left v).integrable_comp_of_integrable hi
  exact hs.integrableOn.congr_fun (fun p hp => translated_cutoff_eq hd q e v p hp) measurableSet_ball

theorem integral_kernel_translatedDisk_le {q d : ℝ} (hq : q < 2) (hd : 0 < d)
    (e : Transverse) (he : ‖e‖ = 1) (v : Transverse) :
    (∫ p in ball (0 : Transverse) d, kernel q e (v - p)) ≤ (‖v‖ + d) * angularMass q := by
  have hD : 0 < ‖v‖ + d := by positivity
  let f := (ball (0 : Transverse) (‖v‖ + d)).indicator (kernel q e)
  have hi : Integrable f :=
    (integrableOn_kernel_centeredDisk hq hD e he).integrable_indicator measurableSet_ball
  have hs := ((volume : Measure Transverse).measurePreserving_sub_left v).integrable_comp_of_integrable hi
  calc
    _ = ∫ p in ball (0 : Transverse) d, f (v - p) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro p hp
      exact (translated_cutoff_eq hd q e v p hp).symm
    _ ≤ ∫ p, f (v - p) :=
      setIntegral_le_integral hs (ae_of_all _ (fun p =>
        indicator_nonneg (fun n _ => kernel_nonneg q e n) (v - p)))
    _ = ∫ n, f n :=
      ((volume : Measure Transverse).measurePreserving_sub_left v).integral_comp
        (Homeomorph.subLeft v).measurableEmbedding f
    _ = _ := by
      rw [integral_indicator measurableSet_ball, integral_kernel_centeredDisk hq hD e he]

def direction (v : Transverse) : Transverse := ‖v‖⁻¹ • v

theorem norm_direction {v : Transverse} (hv : v ≠ 0) : ‖direction v‖ = 1 :=
  norm_smul_inv_norm hv

private theorem direction_inner_self {v : Transverse} (hv : v ≠ 0) :
    inner ℝ (direction v) v = ‖v‖ := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [direction, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

private theorem kernel_small_shift_le {q : ℝ} (hq : 1 < q)
    {v p : Transverse} (hv : v ≠ 0) (hp : ‖p‖ ≤ ‖v‖ / 2) :
    kernel q (direction v) (v - p) ≤ 2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) / ‖v‖ := by
  have hv₀ : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have he : ‖direction v‖ = 1 := norm_direction hv
  have hip : inner ℝ (direction v) p ≤ ‖p‖ := by
    have h := abs_real_inner_le_norm (direction v) p
    rw [he, one_mul] at h
    exact (le_abs_self _).trans h
  have hilow : ‖v‖ / 2 ≤ inner ℝ (direction v) (v - p) := by
    rw [inner_sub_right, direction_inner_self hv]
    linarith
  have hnn : ‖v‖ / 2 ≤ ‖v - p‖ := by
    have h := abs_real_inner_le_norm (direction v) (v - p)
    rw [he, one_mul] at h
    exact hilow.trans ((le_abs_self _).trans h)
  have hn₀ : 0 < ‖v - p‖ := lt_of_lt_of_le (by positivity) hnn
  have hnupper : ‖v - p‖ ≤ ‖v‖ + ‖p‖ := norm_sub_le v p
  have hcos : (1 / 3 : ℝ) ≤ |inner ℝ (direction v) (direction (v - p))| := by
    have hinner : inner ℝ (direction v) (direction (v - p)) =
        inner ℝ (direction v) (v - p) / ‖v - p‖ := by
      simp only [direction, inner_smul_right, div_eq_mul_inv]
      ring
    rw [hinner]
    apply le_trans _ (le_abs_self _)
    apply (le_div_iff₀ hn₀).mpr
    nlinarith
  have hpow : |inner ℝ (direction v) (direction (v - p))| ^ (1 - q) ≤
      (1 / 3 : ℝ) ^ (1 - q) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hcos (by linarith)
  calc
    _ ≤ (1 + (1 / 3 : ℝ) ^ (1 - q)) / ‖v - p‖ := by
      apply div_le_div_of_nonneg_right _ hn₀.le
      change 1 + |inner ℝ (direction v) (direction (v - p))| ^ (1 - q) ≤ _
      linarith
    _ ≤ (1 + (1 / 3 : ℝ) ^ (1 - q)) / (‖v‖ / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hnn
    _ = _ := by field_simp

/-- A single constant works for small disks, large disks, and the atom at zero. -/
def expectationConstant (q : ℝ) : ℝ :=
  2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) + 6 * angularMass q / Real.pi

theorem expectationConstant_pos (q : ℝ) : 0 < expectationConstant q := by
  unfold expectationConstant
  have hM := angularMass_pos q
  positivity

/-- The uniform disk case of `ker:transverse-expectation`, with explicit integrability above. -/
theorem uniformDisk_expectation_le {q d : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d)
    {v : Transverse} (hv : v ≠ 0) :
    (∫ p in ball (0 : Transverse) d, kernel q (direction v) (v - p)) / (Real.pi * d ^ 2) ≤
      expectationConstant q / ‖v‖ := by
  have hv₀ : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have he : ‖direction v‖ = 1 := norm_direction hv
  have hden : 0 < Real.pi * d ^ 2 := by positivity
  have hM : 0 < angularMass q := angularMass_pos q
  have hsmall : 0 ≤ 2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) := by positivity
  by_cases hdsmall : d ≤ ‖v‖ / 2
  · have hi := integrableOn_kernel_translatedDisk hq₂ hd (direction v) he v
    have hc : IntegrableOn
        (fun _ : Transverse => 2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) / ‖v‖)
        (ball (0 : Transverse) d) := integrableOn_const measure_ball_lt_top.ne
    have hb : (∫ p in ball (0 : Transverse) d, kernel q (direction v) (v - p)) ≤
        Real.pi * d ^ 2 * (2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) / ‖v‖) := by
      calc
        _ ≤ ∫ _p in ball (0 : Transverse) d,
            2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) / ‖v‖ :=
          setIntegral_mono_on hi hc measurableSet_ball (fun p hp =>
            kernel_small_shift_le hq₁ hv ((mem_ball_zero_iff.mp hp).le.trans hdsmall))
        _ = _ := by
          rw [setIntegral_const, smul_eq_mul, TransverseDisk.disk_volume_real 0 hd.le]
    have hn : (∫ p in ball (0 : Transverse) d, kernel q (direction v) (v - p)) /
        (Real.pi * d ^ 2) ≤ 2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) / ‖v‖ := by
      apply (div_le_iff₀ hden).mpr
      nlinarith [hb]
    apply hn.trans
    apply div_le_div_of_nonneg_right _ hv₀.le
    unfold expectationConstant
    have h : 0 ≤ 6 * angularMass q / Real.pi := by positivity
    linarith
  · have hrd : ‖v‖ ≤ 2 * d := by linarith
    have hb := integral_kernel_translatedDisk_le hq₂ hd (direction v) he v
    have hb' : (∫ p in ball (0 : Transverse) d, kernel q (direction v) (v - p)) ≤
        3 * d * angularMass q := by
      have h := mul_le_mul_of_nonneg_right (show ‖v‖ + d ≤ 3 * d by linarith) hM.le
      exact hb.trans h
    have hratio : (3 * d * angularMass q) / (Real.pi * d ^ 2) ≤
        (6 * angularMass q / Real.pi) / ‖v‖ := by
      apply (div_le_div_iff₀ hden hv₀).mpr
      rw [← mul_assoc (6 * angularMass q / Real.pi) Real.pi,
        div_mul_cancel₀ _ Real.pi_ne_zero]
      have h := mul_le_mul_of_nonneg_left hrd
        (show 0 ≤ 3 * d * angularMass q by positivity)
      nlinarith
    apply (div_le_div_of_nonneg_right hb' hden.le).trans (hratio.trans _)
    apply div_le_div_of_nonneg_right _ hv₀.le
    unfold expectationConstant
    linarith

theorem kernel_at_zero_input (q : ℝ) {v : Transverse} (hv : v ≠ 0) :
    kernel q (direction v) v = 2 / ‖v‖ := by
  have hn := norm_direction hv
  change (1 + |inner ℝ (direction v) (direction v)| ^ (1 - q)) / ‖v‖ = 2 / ‖v‖
  simp only [real_inner_self_eq_norm_sq, hn, one_pow,
    abs_one, Real.one_rpow, one_add_one_eq_two]

theorem atomZero_expectation_le (q : ℝ) {v : Transverse} (hv : v ≠ 0) :
    (∫ p, kernel q (direction v) (v - p) ∂Measure.dirac (0 : Transverse)) ≤
      expectationConstant q / ‖v‖ := by
  rw [integral_dirac, sub_zero, kernel_at_zero_input q hv]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  unfold expectationConstant
  have hM := angularMass_pos q
  have hr : 0 ≤ (1 / 3 : ℝ) ^ (1 - q) := by positivity
  have h : 0 ≤ 6 * angularMass q / Real.pi := by positivity
  linarith

end BoltzmannNonuniqueness.TransverseAverage

end

end

end OAI
