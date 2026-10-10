import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.FlatAnnularAlternativeEvents

namespace OAI

/-!
# A uniform flat-ball or large-annulus alternative

Compactness upgrades the local annular flat-ball theorem to a radius chosen uniformly
before the measure. A counterexample sequence would converge to a measure with bounded
annular transforms but no admissible flat ball, contradicting the local theorem.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem exists_uniform_flat_annular_radius {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (C G H B cap ε : ℝ) (hC : 0 < C) (hH : 0 < H) (hcap : 0 < cap) (hε : 0 < ε)
    (U : Set (Ambient d)) (hU : IsOpen U) (hzeroU : (0 : Ambient d) ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < cap ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth n G μ → CappedLowerGrowth n C H μ → (0 : Ambient d) ∈ μ.support →
      HasFlatBallAbove n μ U ρ cap ε ∨ HasLargeSmoothAnnulusAbove n μ U ρ cap B := by
  by_contra hnone
  have hcounter (ρ : ℝ) (hρ : 0 < ρ) (hρcap : ρ < cap) :
      ∃ μ : Measure (Ambient d), GlobalUpperGrowth n G μ ∧ CappedLowerGrowth n C H μ ∧
        (0 : Ambient d) ∈ μ.support ∧ ¬ HasFlatBallAbove n μ U ρ cap ε ∧
          ¬ HasLargeSmoothAnnulusAbove n μ U ρ cap B := by
    by_contra hno
    apply hnone
    refine ⟨ρ, hρ, hρcap, ?_⟩
    intro μ hg hl hz
    by_contra hneither
    exact hno ⟨μ, hg, hl, hz, (not_or.mp hneither).1, (not_or.mp hneither).2⟩
  let rseq := fun j : ℕ => (cap / 2) * (1 / 2 : ℝ) ^ j
  have hrseq (j : ℕ) : 0 < rseq j := by dsimp only [rseq]; positivity
  have hrseqcap (j : ℕ) : rseq j < cap := by
    have hhalf : rseq j ≤ cap / 2 :=
      (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)).trans_eq
        (mul_one (cap / 2))
    linarith
  have hrseq0 : Tendsto rseq atTop (𝓝 0) := by
    simpa only [mul_zero] using!
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (cap / 2)
  choose μ hg hl hz hflat hann using fun j => hcounter (rseq j) (hrseq j) (hrseqcap j)
  obtain ⟨τ, hτ, ν, hfinite, _, hlocal, hgν, hlν, hzν⟩ :=
    exists_capped_lower_measure_limit n C G H μ hC hH hg hl hz
  let := hfinite
  let : ∀ j, IsFiniteMeasureOnCompacts (μ (τ j)) := fun j =>
    globalGrowth_finite_on_compacts G _ (hg (τ j))
  have hrseqτ : Tendsto (fun j => rseq (τ j)) atTop (𝓝 0) := hrseq0.comp hτ.tendsto_atTop
  have hannν : ∀ x ∈ ν.support, x ∈ U → ∀ r R : ℝ, ∀ hr : 0 < r, ∀ hrR : r ≤ R,
      R < cap → ‖smoothAnnularTransform n ν x r R hr (hr.trans_le hrR)‖ ≤ B := by
    intro x hx hxU r R hr hrR hRcap
    apply smoothAnnularTransform_bound_at_limit_support n G B (fun j => μ (τ j)) ν
      (fun j => hg (τ j)) hlocal U hU x hx hxU r R hr hrR
    filter_upwards [hrseqτ.eventually (gt_mem_nhds hr)] with j hj
    intro y hy hyU
    exact not_large_smooth_annulus_above_bound n (μ (τ j)) U (rseq (τ j)) cap B (hann (τ j))
      y hy hyU r R hr hrR hj.le hRcap
  have hbadν : ∀ x ∈ ν.support, x ∈ U → ∀ r : ℝ, 0 < r → r < cap →
      min ε 1 / 64 ≤ bilateralBeta n ν x r := by
    intro x hx hxU r hr hrcap
    have hbadj : ∀ᶠ j in atTop, ∀ y ∈ (μ (τ j)).support, y ∈ U →
        min ε 1 ≤ bilateralBeta n (μ (τ j)) y (r / 2) := by
      filter_upwards [hrseqτ.eventually (gt_mem_nhds (by positivity : 0 < r / 2))] with j hj
      intro y hy hyU
      exact (min_le_left ε 1).trans
        (not_flat_ball_above_beta_lower n (μ (τ j)) U (rseq (τ j)) cap ε (hflat (τ j))
          y hy hyU (r / 2) (by positivity) hj.le (by linarith))
    have ht := compactTestConvergence_capped_beta_lower hnd C H (fun j => μ (τ j)) ν
      hlocal hC hH (fun j => hl (τ j)) U hU (min ε 1) (lt_min hε zero_lt_one) (min_le_right _ _)
      (r / 2) (by positivity) hbadj x hx hxU
    simpa only [mul_div_cancel₀ r (by norm_num : (2 : ℝ) ≠ 0)] using! ht
  obtain ⟨b, hb, hbU, r, hr, hrcap, hsmall⟩ :=
    exists_local_flat_ball_of_annular_bound hn hnd (C * 4 ^ n) (G * 2 ^ n) H B cap ν
      (by positivity) hH hgν hlν U hU 0 hzν hzeroU hcap hannν cap (min ε 1 / 64) hcap (by positivity)
  exact (not_lt_of_ge (hbadν b hb hbU r hr hrcap)) hsmall

end

end RieszRectifiability

end OAI
