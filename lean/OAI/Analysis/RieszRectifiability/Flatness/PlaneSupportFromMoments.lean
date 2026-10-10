import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LeastSquaredExcess
import OAI.Analysis.RieszRectifiability.Kernel.BoundedBoxHeight

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem lipschitz_square_energy_lower_bound {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : Ambient d → ℝ) (hf : LipschitzWith 1 f)
    (s : Set (Ambient d)) (hi : IntegrableOn (fun y => f y ^ 2) s μ)
    (x : Ambient d) (ε r c : ℝ) (hε : 0 ≤ ε) (hr : r ≤ ε / 2)
    (hsub : ball x r ⊆ s) (hmass : c ≤ μ.real (ball x r)) (hlarge : ε ≤ f x) :
    (ε / 2) ^ 2 * c ≤ ∫ y in s, f y ^ 2 ∂μ := by
  have hpoint : ∀ y ∈ ball x r, (ε / 2) ^ 2 ≤ f y ^ 2 := by
    intro y hy
    have hd : dist x y ≤ r := by
      simpa only [dist_comm] using! (show dist y x < r from hy).le
    have hdiff : f x - f y ≤ dist x y := by
      have h := hf.dist_le_mul x y
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
      exact (le_abs_self _).trans h
    have hfy : ε / 2 ≤ f y := by linarith
    nlinarith [sq_nonneg (f y - ε / 2)]
  have hfinite : μ (ball x r) ≠ ∞ := ne_of_lt
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top)
  calc
    _ ≤ (ε / 2) ^ 2 * μ.real (ball x r) :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg _)
    _ ≤ ∫ y in ball x r, f y ^ 2 ∂μ :=
      setIntegral_ge_of_const_le_real measurableSet_ball hfinite hpoint
        (IntegrableOn.mono_set hi hsub)
    _ ≤ _ := setIntegral_mono_set hi (Eventually.of_forall fun y => sq_nonneg (f y))
      (Eventually.of_forall fun y hy => hsub hy)

theorem small_square_integrals_force_support_tube {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (f : ℕ → Ambient d → ℝ) (hf : ∀ j, LipschitzWith 1 (f j))
    (a : Ambient d) (R : ℝ)
    (hi : ∀ j, IntegrableOn (fun x => f j x ^ 2) (ball a (R + 1)) (μ j))
    (hlim : Tendsto (fun j => ∫ x in ball a (R + 1), f j x ^ 2 ∂μ j) atTop (𝓝 0))
    (hball : ∀ r : ℝ, 0 < r → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → c ≤ (μ j).real (ball x r))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → f j x < ε := by
  let r := min 1 (ε / 2)
  have hr : 0 < r := lt_min zero_lt_one (by positivity)
  obtain ⟨c, hc, hbc⟩ := hball r hr
  have ht : 0 < (ε / 2) ^ 2 * c := mul_pos (sq_pos_of_pos (by positivity)) hc
  filter_upwards [hbc, hlim.eventually (gt_mem_nhds ht)] with j hj hsmall
  intro x hx hxsupport
  by_contra hlarge
  have hsub : ball x r ⊆ ball a (R + 1) := by
    intro y hy
    have htri := dist_triangle y x a
    have hy' : dist y x < r := hy
    have hx' : dist x a < R := hx
    have hr1 : r ≤ 1 := min_le_left _ _
    exact mem_ball.mpr (by linarith)
  have h := lipschitz_square_energy_lower_bound (μ j) (f j) (hf j)
    (ball a (R + 1)) (hi j) x ε r c hε.le (min_le_right _ _) hsub
    (hj x hx hxsupport) (le_of_not_gt hlarge)
  exact (not_lt_of_ge h) hsmall

theorem moving_plane_support_tube_of_moments {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, (S j : Set (Ambient d)).Nonempty)
    (a : Ambient d) (R : ℝ)
    (hlim : Tendsto (fun j => ∫ x in ball a (R + 1),
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support →
      infDist x (S j : Set (Ambient d)) < ε := by
  apply small_square_integrals_force_support_tube μ
    (fun j x => infDist x (S j : Set (Ambient d))) (fun j => lipschitz_infDist_pt _)
    a R (fun j => squared_infDist_integrableOn_ball (μ j) a (R + 1) _ (hS j)) hlim _ ε hε
  intro r hr
  obtain ⟨c, hc, hbc⟩ := eventual_lower_ball_mass_of_AD_lower n μ C hC hlower hdiam r hr
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbc] with j hj
  exact fun x _ hx => hj x hx

end

end RieszRectifiability

end OAI
