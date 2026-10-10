import OAI.NumberTheory.JointDickman.Arithmetic.RoughDensityRegularity

namespace OAI

/-! # Control of the density down to the shrinking lower endpoint -/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- The higher coefficients still vanish after the loss at `s=B^(-1/10)`. -/
theorem scaledRoughCoefficient_weighted_succ_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (c : ℕ → ℝ) {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (j : ℕ) :
    Tendsto (fun B => scaledRoughCoefficient c z (j + 1) B *
      (B : ℝ) ^ ((j + 1 : ℕ) / 10 : ℝ)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := roughCoefficient_bound hM c hz hzhalf (j + 1)
  let a : ℝ := (9 / 10 : ℝ) * (j + 1 : ℕ) - z
  let r : ℝ := Real.exp 1 + (j + 1 : ℕ)
  have ha : 0 < a := by dsimp [a]; push_cast; linarith [Nat.cast_nonneg j (α := ℝ)]
  have hlimit := ((log_power_div_power_tendsto_zero r ha).const_mul
    (C * (1000 : ℝ) ^ r)).comp tendsto_natCast_atTop_atTop
  simp only [mul_zero] at hlimit
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlimit
  have hP : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  have hlogP : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hP, hlogP, eventually_gt_atTop 1] with B hp hlog hB
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hQ := primeNormalizer_bounds _ (auxiliaryPrimes_prime B) hz (by linarith : z ≤ 1)
  have hb := hbound (auxiliaryCutoff B) hp hlog
  rw [Real.norm_eq_abs, abs_mul, scaledRoughCoefficient, abs_mul, abs_mul,
    abs_of_nonneg hQ.1, abs_of_pos (Real.rpow_pos_of_pos hB0 _),
    abs_of_pos (Real.rpow_pos_of_pos hB0 _)]
  calc
    _ ≤ 1 * (C * (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + (j + 1 : ℕ))) *
        (B : ℝ) ^ (z - (j + 1 : ℕ)) * (B : ℝ) ^ ((j + 1 : ℕ) / 10 : ℝ) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul hQ.2 hb (abs_nonneg _) (by norm_num)) (Real.rpow_nonneg hB0.le _))
        (Real.rpow_nonneg hB0.le _)
    _ = C * (1000 : ℝ) ^ r * ((Real.log B) ^ r / (B : ℝ) ^ a) := by
      have hcut : Real.log (auxiliaryCutoff B) = 1000 * Real.log B := by
        simp only [auxiliaryCutoff, Nat.cast_pow, Real.log_pow]; norm_num
      rw [one_mul, hcut, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) (Real.log_pos hBreal).le,
        mul_assoc, ← Real.rpow_add hB0]
      have hexp : z - (j + 1 : ℕ) + ((j + 1 : ℕ) / 10 : ℝ) = -a := by dsimp [a]; ring
      rw [hexp, Real.rpow_neg hB0.le]
      dsimp [r]
      ring


noncomputable def shrinkingDensityError (c : ℕ → ℝ) (z k : ℝ) (H B : ℕ) : ℝ :=
  (∑ j ∈ range (H + 1),
    |scaledRoughCoefficient c z j B - (if j = 0 then k else 0)| * (B : ℝ) ^ ((j : ℝ) / 10)) +
  ∑ j ∈ range (H + 1), |scaledRoughCoefficient c z j B / B * (z - 1 - j)| *
    (B : ℝ) ^ (((j : ℝ) + 1) / 10)

theorem shrinkingDensityError_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (H : ℕ) :
    Tendsto (fun B => shrinkingDensityError c z
      ((4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)) H B)
      atTop (𝓝 0) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let b : ℕ → ℝ := fun j => if j = 0 then k else 0
  have hcoef (j : ℕ) : Tendsto
      (fun B => scaledRoughCoefficient c z j B * (B : ℝ) ^ ((j : ℝ) / 10)) atTop (𝓝 (b j)) := by
    cases j with
    | zero => simpa [b, k] using scaledRoughCoefficient_zero_tendsto hM hMP c hc hz (by linarith)
    | succ j => simpa [b] using scaledRoughCoefficient_weighted_succ_tendsto hM c hz.le hzhalf j
  have hfirst (j : ℕ) : Tendsto
      (fun B => |scaledRoughCoefficient c z j B - b j| * (B : ℝ) ^ ((j : ℝ) / 10)) atTop (𝓝 0) := by
    cases j with
    | zero => simpa [b] using ((hcoef 0).sub_const (b 0)).abs
    | succ j =>
        convert (hcoef (j + 1)).abs using 1
        · funext B
          simp [b, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg B) _)]
        · simp [b]
  have hsecond (j : ℕ) : Tendsto
      (fun B => |scaledRoughCoefficient c z j B / B * (z - 1 - j)| *
        (B : ℝ) ^ (((j : ℝ) + 1) / 10)) atTop (𝓝 0) := by
    have hpow := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp
      tendsto_natCast_atTop_atTop
    have hh := ((hcoef j).mul_const (z - 1 - j)).mul hpow
    simp only [mul_zero] at hh
    have hhabs := hh.abs
    simp only [abs_zero] at hhabs
    apply hhabs.congr'
    filter_upwards [eventually_gt_atTop 0] with B hB
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    have heq : (B : ℝ) ^ ((j : ℝ) / 10) * (B : ℝ) ^ (-(9 / 10 : ℝ)) =
        (B : ℝ) ^ (((j : ℝ) + 1) / 10) / B := by
      rw [← Real.rpow_add hB0]
      have hexp : (j : ℝ) / 10 + -(9 / 10 : ℝ) = ((j : ℝ) + 1) / 10 - 1 := by ring
      rw [hexp, Real.rpow_sub_one hB0.ne']
    dsimp only [Function.comp_def]
    rw [abs_mul, abs_mul, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hB0 _), abs_of_pos (Real.rpow_pos_of_pos hB0 _),
      abs_mul, abs_div, abs_of_pos hB0]
    rw [mul_right_comm (|scaledRoughCoefficient c z j B|), mul_assoc,
      mul_assoc, heq]
    ring
  have h1 := tendsto_finsetSum (range (H + 1)) (fun j _ => hfirst j)
  have h2 := tendsto_finsetSum (range (H + 1)) (fun j _ => hsecond j)
  simpa only [sum_const_zero, add_zero, shrinkingDensityError, b, k] using h1.add h2

theorem scaledRoughDensity_ratio (c : ℕ → ℝ) (z k : ℝ) (H B : ℕ)
    {s : ℝ} (hs : 0 < s) :
    scaledRoughDensity c z H B s / s ^ (z - 1) - k =
      (∑ j ∈ range (H + 1),
        (scaledRoughCoefficient c z j B - if j = 0 then k else 0) * s ^ (-(j : ℝ))) +
      ∑ j ∈ range (H + 1),
        (scaledRoughCoefficient c z j B / B * (z - 1 - j)) * s ^ (-((j : ℝ) + 1)) := by
  have hp (j : ℝ) : s ^ (z - 1 - j) / s ^ (z - 1) = s ^ (-j) := by
    rw [← Real.rpow_sub hs]
    congr 1
    ring
  have hp' (j : ℝ) : s ^ (z - 2 - j) / s ^ (z - 1) = s ^ (-(j + 1)) := by
    rw [← Real.rpow_sub hs]
    congr 1
    ring
  simp only [scaledRoughDensity, add_div, sum_div, mul_div_assoc, hp, hp', sub_mul, sum_sub_distrib]
  simp
  ring

/-- The relative error is small uniformly down to `s=B^(-1/10)`. -/
theorem scaledRoughDensity_ratio_error (c : ℕ → ℝ) (z k : ℝ) (H B : ℕ)
    (hB : 0 < B) {s : ℝ} (hs : (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ s) :
    |scaledRoughDensity c z H B s / s ^ (z - 1) - k| ≤ shrinkingDensityError c z k H B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hbase : 0 < (B : ℝ) ^ (-(1 / 10 : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have hs0 : 0 < s := hbase.trans_le hs
  have hp (d : ℝ) (hd : 0 ≤ d) : s ^ (-d) ≤ (B : ℝ) ^ (d / 10) := by
    have h := Real.rpow_le_rpow_of_nonpos hbase hs (neg_nonpos.mpr hd)
    rw [← Real.rpow_mul hB0.le] at h
    convert h using 1
    congr 1
    ring
  rw [scaledRoughDensity_ratio c z k H B hs0]
  apply (abs_add_le _ _).trans
  unfold shrinkingDensityError
  apply add_le_add
  · apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro j _
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    exact mul_le_mul_of_nonneg_left (hp j (Nat.cast_nonneg j)) (abs_nonneg _)
  · apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro j _
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    exact mul_le_mul_of_nonneg_left (hp (j + 1) (by positivity)) (abs_nonneg _)


/-- Positivity and the singular power bound hold all the way down to the
moving lower boundary, uniformly in the scale. -/
theorem scaledRoughDensity_shrinking_bounds
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ s : ℝ,
      (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ s →
      0 < scaledRoughDensity c z H B s ∧
        scaledRoughDensity c z H B s ≤ K * s ^ (z - 1) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  have hk : 0 < k := mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (div_pos (Real.exp_pos _) (Real.Gamma_pos_of_pos hz))
  refine ⟨2 * k, by positivity, ?_⟩
  have hlim := shrinkingDensityError_tendsto hM hMP c hc hz hzhalf H
  have hsmall : ∀ᶠ B : ℕ in atTop, shrinkingDensityError c z k H B < k / 2 :=
    hlim.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < k / 2))
  filter_upwards [hsmall, eventually_gt_atTop 0] with B hsmallB hB
  intro s hs
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hs0 : 0 < s := (Real.rpow_pos_of_pos hB0 _).trans_le hs
  have hp : 0 < s ^ (z - 1) := Real.rpow_pos_of_pos hs0 _
  have h := abs_le.mp (scaledRoughDensity_ratio_error c z k H B hB hs)
  have hratio : 0 < scaledRoughDensity c z H B s / s ^ (z - 1) := by linarith
  refine ⟨(div_pos_iff_of_pos_right hp).mp hratio, ?_⟩
  apply (div_le_iff₀ hp).mp
  linarith

end JointDickman

end OAI
