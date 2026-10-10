import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.WeightedGramBessel
import OAI.Analysis.RieszRectifiability.Foundations.PlanarPullbackMeasure

namespace OAI

/-!
# Mean-zero pairing decay

Cancellation against constants turns Lipschitz control into a radius gain for pairings
with mean-zero functions. Support-ball mass and growth bounds further control these
pairings in terms of the support radius and the uniform size of the mean-zero function.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal ENNReal

theorem mean_zero_lipschitz_pairing_bound {d : ℕ} (μ : Measure (Ambient d))
    (f g : Ambient d → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hgI : Integrable g μ) (hzero : (∫ x, g x ∂μ) = 0)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (z : Ambient d) (R : ℝ)
    (hs : ∀ x, g x ≠ 0 → dist x z ≤ R) :
    |∫ x, f x * g x ∂μ| ≤ (L : ℝ) * R * ∫ x, |g x| ∂μ := by
  have hfg : Integrable (fun x => f x * g x) μ := memLp_one_iff_integrable.mp (hf.mul hg)
  have hsub : Integrable (fun x => (f x - f z) * g x) μ := by
    simpa only [sub_mul] using! hfg.sub (hgI.const_mul (f z))
  have heq : (∫ x, (f x - f z) * g x ∂μ) = ∫ x, f x * g x ∂μ := by
    simp only [sub_mul]
    rw [integral_sub hfg (hgI.const_mul (f z)), integral_const_mul, hzero, mul_zero, sub_zero]
  rw [← heq]
  calc
    _ ≤ ∫ x, |(f x - f z) * g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ((L : ℝ) * R) * |g x| ∂μ := by
      apply integral_mono hsub.abs (hgI.abs.const_mul _)
      intro x
      change |(f x - f z) * g x| ≤ (L : ℝ) * R * |g x|
      by_cases hx : g x = 0
      · simp only [hx, mul_zero, abs_zero, le_refl]
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have h := hLip.dist_le_mul x z
      rw [Real.dist_eq] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hs x hx) L.coe_nonneg)
    _ = _ := integral_const_mul _ _

theorem integral_abs_le_support_ball_mass {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (g : Ambient d → ℝ) (hg : Integrable g μ)
    (z : Ambient d) (R A : ℝ) (hbound : ∀ x, |g x| ≤ A)
    (hs : ∀ x, g x ≠ 0 → x ∈ ball z R) :
    (∫ x, |g x| ∂μ) ≤ A * μ.real (ball z R) := by
  have : IsFiniteMeasure (μ.restrict (ball z R)) := isFiniteMeasure_restrict.mpr
    (ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall z R).measure_lt_top))
  have heq : (∫ x in ball z R, |g x| ∂μ) = ∫ x, |g x| ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : g x = 0 := by by_contra hn; exact hx (hs x hn)
    rw [hz, abs_zero]
  rw [← heq]
  calc
    _ ≤ ∫ _x in ball z R, A ∂μ := integral_mono hg.abs.restrict (integrable_const _)
      (fun x => hbound x)
    _ = _ := by
      rw [integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm]

theorem compact_lipschitz_test_memLp {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : Ambient d → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L f)
    (z : Ambient d) (R : ℝ) (hs : tsupport f ⊆ ball z R) :
    MemLp f 2 μ ∧ Integrable f μ := by
  have hc : HasCompactSupport f :=
    (isCompact_closedBall z R).of_isClosed_subset (isClosed_tsupport f) (hs.trans ball_subset_closedBall)
  exact ⟨hLip.continuous.memLp_of_hasCompactSupport hc,
    hLip.continuous.integrable_of_hasCompactSupport hc⟩

theorem mean_zero_gram_bound_of_growth {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth n G μ)
    (f g : Ambient d → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hgI : Integrable g μ) (hzero : (∫ x, g x ∂μ) = 0)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (z : Ambient d) (R A : ℝ)
    (hR : 0 < R) (hA : 0 ≤ A) (hbound : ∀ x, |g x| ≤ A)
    (hs : ∀ x, g x ≠ 0 → x ∈ ball z R) :
    |∫ x, f x * g x ∂μ| ≤ ((L : ℝ) * R * A) * (G * R ^ n) := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hgrowth
  have hm : μ.real (ball z R) ≤ G * R ^ n :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hgrowth.1 (pow_nonneg hR.le n))
      (hgrowth.2 z R hR)
  calc
    _ ≤ (L : ℝ) * R * ∫ x, |g x| ∂μ := mean_zero_lipschitz_pairing_bound μ f g hf hg hgI hzero
      L hLip z R (fun x hx => (hs x hx).le)
    _ ≤ (L : ℝ) * R * (A * (G * R ^ n)) :=
      mul_le_mul_of_nonneg_left ((integral_abs_le_support_ball_mass μ g hgI z R A hbound hs).trans
        (mul_le_mul_of_nonneg_left hm hA)) (mul_nonneg L.coe_nonneg hR.le)
    _ = _ := by ring

theorem integral_pairing_zero_of_disjoint_support {d : ℕ} (μ : Measure (Ambient d))
    (f g : Ambient d → ℝ) (hs : Disjoint (Function.support f) (Function.support g)) :
    (∫ x, f x * g x ∂μ) = 0 := by
  have hz : (fun x => f x * g x) = 0 := by
    funext x
    by_cases hf : f x = 0
    · simp only [hf, zero_mul, Pi.zero_apply]
    · have hg : g x = 0 := by
        by_contra hg
        exact Set.disjoint_left.mp hs hf hg
      simp only [hg, mul_zero, Pi.zero_apply]
  rw [hz]
  change (∫ _x : Ambient d, (0 : ℝ) ∂μ) = 0
  exact integral_zero _ _

end

end RieszRectifiability

end OAI
