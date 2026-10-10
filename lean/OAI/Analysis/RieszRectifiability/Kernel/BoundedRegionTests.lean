import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LocalizedNormalTest

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

def radialUnitCutoff {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d) : ℝ :=
  max 0 (min 1 (R + 1 - dist x a))

theorem radialUnitCutoff_bounds {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d) :
    0 ≤ radialUnitCutoff a R x ∧ radialUnitCutoff a R x ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem radialUnitCutoff_eq_one {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d)
    (hx : dist x a ≤ R) : radialUnitCutoff a R x = 1 := by
  have h : (1 : ℝ) ≤ R + 1 - dist x a := by linarith
  simp only [radialUnitCutoff, min_eq_left h, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem radialUnitCutoff_support_bound {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d)
    (hx : radialUnitCutoff a R x ≠ 0) : dist x a ≤ R + 1 := by
  by_contra h
  have hneg : R + 1 - dist x a < 0 := by linarith
  have hmin : min 1 (R + 1 - dist x a) ≤ 0 := (min_le_right _ _).trans hneg.le
  exact hx (max_eq_left hmin)

theorem radialUnitCutoff_lipschitz {d : ℕ} (a : Ambient d) (R : ℝ) :
    LipschitzWith 1 (radialUnitCutoff a R) := by
  have h : LipschitzWith 1 (fun x : Ambient d => R + 1 - dist x a) := by
    simpa using! (LipschitzWith.const (R + 1)).sub (LipschitzWith.dist_left a)
  exact (h.const_min 1).const_max 0

theorem radialUnitCutoff_hasCompactSupport {d : ℕ} (a : Ambient d) (R : ℝ) :
    HasCompactSupport (radialUnitCutoff a R) := by
  apply HasCompactSupport.intro (isCompact_closedBall a (R + 1))
  intro x hx
  by_contra h
  exact hx (radialUnitCutoff_support_bound a R x h)

theorem exists_compact_lipschitz_test_on_ball {d : ℕ} (a : Ambient d) (R : ℝ)
    (ψ : Ambient d → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ) :
    ∃ (g : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport g ∧ LipschitzWith K g ∧
      (∀ x, |g x| ≤ (B : ℝ)) ∧ ∀ x ∈ ball a R, g x = ψ x := by
  let χ := radialUnitCutoff a R
  let B : ℝ≥0 := Real.toNNReal ((L : ℝ) * (R + 1) + |ψ a|)
  have hχ : LipschitzWith 1 χ := radialUnitCutoff_lipschitz a R
  have hχB : ∀ x, |χ x| ≤ (1 : ℝ≥0) := by
    intro x
    change |radialUnitCutoff a R x| ≤ 1
    rw [abs_of_nonneg (radialUnitCutoff_bounds a R x).1]
    exact (radialUnitCutoff_bounds a R x).2
  have hB : ∀ x, χ x ≠ 0 → |ψ x| ≤ (B : ℝ) := by
    intro x hx
    have hdist : dist x a ≤ R + 1 := radialUnitCutoff_support_bound a R x hx
    have hdiff : |ψ x - ψ a| ≤ (L : ℝ) * dist x a := by
      simpa only [Real.dist_eq] using! hψ.dist_le_mul x a
    calc
      |ψ x| ≤ |ψ x - ψ a| + |ψ a| := by simpa only [sub_add_cancel] using! abs_add_le (ψ x - ψ a) (ψ a)
      _ ≤ (L : ℝ) * (R + 1) + |ψ a| :=
        add_le_add (hdiff.trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)) le_rfl
      _ ≤ (B : ℝ) := Real.le_coe_toNNReal _
  refine ⟨fun x => χ x * ψ x, 1 * L + 1 * B, B,
    (radialUnitCutoff_hasCompactSupport a R).mul_right,
    lipschitz_product_of_bound_on_support χ ψ 1 L 1 B hχ hψ hχB hB, ?_, ?_⟩
  · intro x
    by_cases hx : χ x = 0
    · simp only [hx, zero_mul, abs_zero]
      exact B.coe_nonneg
    · calc
        |χ x * ψ x| = |χ x| * |ψ x| := abs_mul _ _
        _ ≤ 1 * (B : ℝ) := mul_le_mul (hχB x) (hB x hx) (abs_nonneg _) (by norm_num)
        _ = _ := one_mul _
  · intro x hx
    change χ x * ψ x = ψ x
    rw [show χ x = 1 from radialUnitCutoff_eq_one a R x hx.le, one_mul]

theorem compact_moments_extend_on_ball {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (a : Ambient d) (R : ℝ)
    (hμ : ∀ j, ∀ᵐ x ∂μ j, x ∈ ball a R) (hν : ∀ᵐ x ∂ν, x ∈ ball a R)
    (w : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hmoment : ∀ (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop (𝓝 (∫ x, v x * ψ x ∂ν))) :
    ∀ (ψ : Ambient d → ℝ) (L : ℝ≥0), LipschitzWith L ψ →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop (𝓝 (∫ x, v x * ψ x ∂ν)) := by
  intro ψ L hψ
  obtain ⟨g, K, B, hgc, hgLip, hgB, heq⟩ := exists_compact_lipschitz_test_on_ball a R ψ L hψ
  have hm : ∀ j, (∫ x, w j x * g x ∂μ j) = ∫ x, w j x * ψ x ∂μ j := by
    intro j
    apply integral_congr_ae
    filter_upwards [hμ j] with x hx
    rw [heq x hx]
  have hn : (∫ x, v x * g x ∂ν) = ∫ x, v x * ψ x ∂ν := by
    apply integral_congr_ae
    filter_upwards [hν] with x hx
    rw [heq x hx]
  simpa only [hm, hn] using! hmoment g K B hgc hgLip hgB

end

end RieszRectifiability

end OAI
