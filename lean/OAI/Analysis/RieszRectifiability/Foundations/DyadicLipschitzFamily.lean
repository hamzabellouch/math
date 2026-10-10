import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.ADInteractionPacking

namespace OAI

/-!
# Normalized dyadic Lipschitz test families

The family packages mean-zero compactly supported tests with dyadic radii, separated
centers, and weights whose squares are the dimensional powers of the radii.
Its support and regularity assumptions give integrability, while global upper growth
gives weighted Gram estimates at both finer and coarser scales.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

structure DyadicLipschitzFamily (ι : Type*) (n d : ℕ) (μ : Measure (Ambient d)) (c J A : ℝ) where
  center : ι → Ambient d
  radius : ι → ℝ
  weight : ι → ℝ
  level : ι → ℕ
  test : ι → Ambient d → ℝ
  lip : ι → ℝ≥0
  radius_pos : ∀ i, 0 < radius i
  weight_pos : ∀ i, 0 < weight i
  weight_sq : ∀ i, weight i ^ 2 = radius i ^ n
  lipschitz : ∀ i, LipschitzWith (lip i) (test i)
  lip_bound : ∀ i, (lip i : ℝ) ≤ A / (radius i * weight i)
  value_bound : ∀ i x, |test i x| ≤ A / weight i
  support_subset : ∀ i, tsupport (test i) ⊆ ball (center i) (J * radius i)
  mean_zero : ∀ i, (∫ x, test i x ∂μ) = 0
  center_mem : ∀ i, center i ∈ μ.support
  core_admissible : ∀ i, AdmissibleRadius μ (c * radius i)
  scale_eq : ∀ i j, level i ≤ level j → radius j = radius i * (1 / 2 : ℝ) ^ (level j - level i)
  separated : ∀ i j, level i = level j → i ≠ j →
    c * radius i + c * radius j ≤ dist (center i) (center j)

theorem DyadicLipschitzFamily.memLp_integrable {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} [IsFiniteMeasureOnCompacts μ] {c J A : ℝ}
    (F : DyadicLipschitzFamily ι n d μ c J A) (i : ι) : MemLp (F.test i) 2 μ ∧ Integrable (F.test i) μ :=
  compact_lipschitz_test_memLp μ (F.test i) (F.lip i) (F.lipschitz i)
    (F.center i) (J * F.radius i) (F.support_subset i)

theorem DyadicLipschitzFamily.support_ball {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ}
    (F : DyadicLipschitzFamily ι n d μ c J A) (i : ι) (x : Ambient d) (hx : F.test i x ≠ 0) :
    x ∈ ball (F.center i) (J * F.radius i) :=
  F.support_subset i (subset_tsupport (F.test i) hx)

theorem DyadicLipschitzFamily.radius_antitone {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ}
    (F : DyadicLipschitzFamily ι n d μ c J A) (i j : ι) (hij : F.level i ≤ F.level j) :
    F.radius j ≤ F.radius i := by
  rw [F.scale_eq i j hij]
  exact mul_le_of_le_one_right (F.radius_pos i).le
    (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1))

theorem DyadicLipschitzFamily.radius_eq_of_level_eq {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ}
    (F : DyadicLipschitzFamily ι n d μ c J A) (i j : ι) (hij : F.level i = F.level j) :
    F.radius i = F.radius j := by
  simpa only [hij, Nat.sub_self, pow_zero, mul_one] using! (F.scale_eq i j hij.le).symm

theorem DyadicLipschitzFamily.fine_gram {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ} (F : DyadicLipschitzFamily ι n d μ c J A)
    (G : ℝ) (hg : GlobalUpperGrowth n G μ) (hJ : 0 < J) (hA : 0 ≤ A) (i j : ι) :
    |∫ x, F.test i x * F.test j x ∂μ| * F.weight j ≤
      (G * J ^ (n + 1) * A ^ 2) * (F.radius j / F.radius i) * (F.weight j ^ 2 / F.weight i) := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  exact normalized_gram_fine_weighted n G μ hg (F.test i) (F.test j)
    (F.memLp_integrable i).1 (F.memLp_integrable j).1 (F.memLp_integrable j).2 (F.mean_zero j)
    (F.lip i) (F.lipschitz i) (F.center j) (F.radius i) (F.radius j) (F.weight i) (F.weight j)
    J A (F.radius_pos i) (F.radius_pos j) (F.weight_pos i) (F.weight_pos j) hJ hA (F.weight_sq j)
    (F.lip_bound i) (F.value_bound j) (F.support_ball j)

theorem DyadicLipschitzFamily.coarse_gram {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ} (F : DyadicLipschitzFamily ι n d μ c J A)
    (G : ℝ) (hg : GlobalUpperGrowth n G μ) (hJ : 0 < J) (hA : 0 ≤ A) (i j : ι) :
    |∫ x, F.test i x * F.test j x ∂μ| * F.weight j ≤
      (G * J ^ (n + 1) * A ^ 2) * (F.radius i / F.radius j) * F.weight i := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  exact normalized_gram_coarse_weighted n G μ hg (F.test i) (F.test j)
    (F.memLp_integrable i).1 (F.memLp_integrable j).1 (F.memLp_integrable i).2 (F.mean_zero i)
    (F.lip j) (F.lipschitz j) (F.center i) (F.radius i) (F.radius j) (F.weight i) (F.weight j)
    J A (F.radius_pos i) (F.radius_pos j) (F.weight_pos i) (F.weight_pos j) hJ hA (F.weight_sq i)
    (F.lip_bound j) (F.value_bound i) (F.support_ball i)

end

end RieszRectifiability

end OAI
