import OAI.NumberTheory.JointDickman.Arithmetic.RoughDensityRegularity

namespace OAI

/-! # The normalization of rough summatory means -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def roughMeanNormalization (B : ℕ) (z : ℝ) : ℝ :=
  Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 - z)

noncomputable def roughMeanProfile (c : ℕ → ℝ) (z : ℝ) (H B : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ range (H + 1), scaledRoughCoefficient c z j B * s ^ (z - 1 - j)

theorem roughMeanNormalization_nonneg (B : ℕ) (z : ℝ) :
    0 ≤ roughMeanNormalization B z := by
  exact mul_nonneg (Real.log_natCast_nonneg _)
    (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg B)
      (mul_nonneg (by norm_num) (Real.log_natCast_nonneg B))) _)

theorem roughMeanNormalization_ratio {B : ℕ} (hB : 1 < B) (z : ℝ) :
    roughMeanNormalization B z / (B : ℝ) = 1 / auxiliaryRatio B ^ z := by
  have hR := auxiliaryRatio_pos hB
  have hmul := auxiliaryRatio_mul_log hB
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hB)
  have hrpow : auxiliaryRatio B ^ (1 - z) * auxiliaryRatio B ^ z = auxiliaryRatio B := by
    rw [← Real.rpow_add hR]
    simp
  unfold roughMeanNormalization
  apply (div_eq_div_iff hB0 (Real.rpow_pos_of_pos hR z).ne').mpr
  calc
    _ = Real.log (auxiliaryCutoff B) *
        (auxiliaryRatio B ^ (1 - z) * auxiliaryRatio B ^ z) := by ring
    _ = B := by rw [hrpow, mul_comm, hmul]
    _ = _ := by ring

theorem roughMeanNormalization_eventually_le {z : ℝ} (hz : 0 ≤ z) :
    ∀ᶠ B : ℕ in atTop, roughMeanNormalization B z ≤ B := by
  filter_upwards [auxiliaryRatio_tendsto.eventually_ge_atTop 1, eventually_gt_atTop 1]
    with B hR hB
  have hp : auxiliaryRatio B ^ (1 - z) ≤ auxiliaryRatio B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hR (show 1 - z ≤ 1 by linarith)
  calc
    _ ≤ Real.log (auxiliaryCutoff B) * auxiliaryRatio B :=
      mul_le_mul_of_nonneg_left hp (Real.log_natCast_nonneg _)
    _ = B := by rw [mul_comm, auxiliaryRatio_mul_log hB]

theorem roughMeanNormalization_quotient_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun B => roughMeanNormalization B z /
      (primeNormalizer (auxiliaryPrimes B) z * B)) atTop (𝓝 ((4 : ℝ) ^ z)) := by
  have hlim := (auxiliary_primeNormalizer_tendsto hM hz hz1).inv₀
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (-z)).ne'
  have heq : (fun B => (primeNormalizer (auxiliaryPrimes B) z * auxiliaryRatio B ^ z)⁻¹) =ᶠ[atTop]
      (fun B => roughMeanNormalization B z / (primeNormalizer (auxiliaryPrimes B) z * B)) := by
    filter_upwards [eventually_gt_atTop 1] with B hB
    conv_rhs => rw [mul_comm (primeNormalizer (auxiliaryPrimes B) z)]
    rw [div_mul_eq_div_div, roughMeanNormalization_ratio hB]
    ring
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)] at hlim
  simpa only [inv_inv] using hlim.congr' heq

theorem roughMeanProfile_eq (c : ℕ → ℝ) (z : ℝ) (H B : ℕ) {s : ℝ}
    (hB : 0 < B) (hs : 0 < s) :
    roughMeanProfile c z H B s = (B : ℝ) * primeNormalizer (auxiliaryPrimes B) z *
      ∑ j ∈ range (H + 1), roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z j *
        ((B : ℝ) * s) ^ (z - 1 - j) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  unfold roughMeanProfile scaledRoughCoefficient
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [Real.mul_rpow hB0.le hs.le]
  have he : (B : ℝ) ^ (z - j) = B * (B : ℝ) ^ (z - 1 - j) := by
    rw [show z - (j : ℝ) = 1 + (z - 1 - j) by ring, Real.rpow_add hB0, Real.rpow_one]
  rw [he]
  ring

theorem roughMeanProfile_eventually_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ B : ℕ in atTop, ∀ s : ℝ, δ ≤ s →
      |roughMeanProfile c z H B s| ≤ M := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let b := fun j : ℕ => if j = 0 then k else 0
  have hcoef (j : ℕ) : Tendsto (fun B => scaledRoughCoefficient c z j B) atTop (𝓝 (b j)) := by
    cases j with
    | zero => exact scaledRoughCoefficient_zero_tendsto hM hMP c hc hz (by linarith)
    | succ j => simpa [b] using scaledRoughCoefficient_succ_tendsto hM c hz.le hzhalf j
  have hunif := finite_power_uniform (range (H + 1)) (fun j => z - 1 - j) b
    (fun B j => scaledRoughCoefficient c z j B) hδ
    (fun j _ => by linarith [Nat.cast_nonneg (α := ℝ) j]) (fun j _ => hcoef j)
  have hlimit : TendstoUniformlyOn (roughMeanProfile c z H) (fun s => k * s ^ (z - 1))
      atTop (Set.Ici δ) := by
    change TendstoUniformlyOn (fun B s => ∑ j ∈ range (H + 1),
      scaledRoughCoefficient c z j B * s ^ (z - 1 - j)) _ _ _
    simpa [b] using hunif
  refine ⟨|k| * δ ^ (z - 1) + 1, by positivity, ?_⟩
  exact uniform_power_eventually_bounded hδ (by linarith) hlimit

end JointDickman

end OAI
