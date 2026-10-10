import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLipschitzAmplitude
import OAI.Analysis.RieszRectifiability.Foundations.DyadicLipschitzFamily

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

structure DyadicOscillationTests (ι : Type*) (d : ℕ)
    (μ : Measure (Ambient d)) (c J : ℝ) where
  center : ι → Ambient d
  radius : ι → ℝ
  level : ι → ℕ
  test : ι → Ambient d → ℝ
  lip : ι → ℝ≥0
  radius_pos : ∀ i, 0 < radius i
  lipschitz : ∀ i, LipschitzWith (lip i) (test i)
  lip_bound : ∀ i, (lip i : ℝ) ≤ 1 / radius i
  support_subset : ∀ i, tsupport (test i) ⊆ ball (center i) (J * radius i)
  mean_zero : ∀ i, (∫ x, test i x ∂μ) = 0
  center_mem : ∀ i, center i ∈ μ.support
  core_admissible : ∀ i, AdmissibleRadius μ (c * radius i)
  scale_eq : ∀ i j, level i ≤ level j →
    radius j = radius i * (1 / 2 : ℝ) ^ (level j - level i)
  separated : ∀ i j, level i = level j → i ≠ j →
    c * radius i + c * radius j ≤ dist (center i) (center j)

def DyadicOscillationTests.weight {ι : Type*} {d : ℕ}
    {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J) (n : ℕ) (i : ι) : ℝ :=
  Real.sqrt (F.radius i ^ n)

theorem DyadicOscillationTests.weight_pos {ι : Type*} {d : ℕ}
    {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J) (n : ℕ) (i : ι) : 0 < F.weight n i := by
  exact Real.sqrt_pos.mpr (pow_pos (F.radius_pos i) n)

theorem DyadicOscillationTests.weight_sq {ι : Type*} {d : ℕ}
    {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J) (n : ℕ) (i : ι) :
    F.weight n i ^ 2 = F.radius i ^ n :=
  Real.sq_sqrt (pow_nonneg (F.radius_pos i).le n)

theorem DyadicOscillationTests.value_bound {ι : Type*} {d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J) (hJ : 0 < J) (i : ι) (x : Ambient d) :
    |F.test i x| ≤ 2 * J :=
  original_oscillation_test_amplitude (F.test i) (F.lip i) (F.lipschitz i)
    (F.center i) (F.radius i) J (F.radius_pos i) hJ (F.lip_bound i) (F.support_subset i) x

def DyadicOscillationTests.normalized {ι : Type*} {d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J) (n : ℕ) (hJ : 0 < J) :
    DyadicLipschitzFamily ι n d μ c J (2 * J + 1) where
  center := F.center
  radius := F.radius
  weight := F.weight n
  level := F.level
  test := fun i x => (F.weight n i)⁻¹ * F.test i x
  lip := fun i => ‖(F.weight n i)⁻¹‖₊ * F.lip i
  radius_pos := F.radius_pos
  weight_pos := F.weight_pos n
  weight_sq := F.weight_sq n
  lipschitz := fun i => lipschitz_const_mul_real (F.lipschitz i) _
  lip_bound := by
    intro i
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (F.weight_pos n i))]
    calc
      _ ≤ (F.weight n i)⁻¹ * (1 / F.radius i) :=
        mul_le_mul_of_nonneg_left (F.lip_bound i) (inv_nonneg.mpr (F.weight_pos n i).le)
      _ = 1 / (F.radius i * F.weight n i) := by ring
      _ ≤ (2 * J + 1) / (F.radius i * F.weight n i) := by
        exact div_le_div_of_nonneg_right (by linarith)
          (mul_nonneg (F.radius_pos i).le (F.weight_pos n i).le)
  value_bound := by
    intro i x
    rw [abs_mul, abs_of_pos (inv_pos.mpr (F.weight_pos n i))]
    calc
      _ ≤ (F.weight n i)⁻¹ * (2 * J) :=
        mul_le_mul_of_nonneg_left (F.value_bound hJ i x) (inv_nonneg.mpr (F.weight_pos n i).le)
      _ ≤ (F.weight n i)⁻¹ * (2 * J + 1) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr (F.weight_pos n i).le)
      _ = _ := by ring
  support_subset := fun i => tsupport_mul_subset_right.trans (F.support_subset i)
  mean_zero := by intro i; rw [integral_const_mul, F.mean_zero i, mul_zero]
  center_mem := F.center_mem
  core_admissible := F.core_admissible
  scale_eq := F.scale_eq
  separated := F.separated

theorem DyadicOscillationTests.normalized_pairing_sq {ι : Type*} {d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J) (n : ℕ) (hJ : 0 < J)
    (i : ι) (u : Ambient d → ℝ) :
    (∫ x, (F.normalized n hJ).test i x * u x ∂μ) ^ 2 =
      (∫ x, F.test i x * u x ∂μ) ^ 2 / F.radius i ^ n := by
  change (∫ x, ((F.weight n i)⁻¹ * F.test i x) * u x ∂μ) ^ 2 = _
  simp_rw [mul_assoc]
  rw [integral_const_mul, mul_pow, inv_pow, F.weight_sq n i]
  ring

end

end RieszRectifiability

end OAI
