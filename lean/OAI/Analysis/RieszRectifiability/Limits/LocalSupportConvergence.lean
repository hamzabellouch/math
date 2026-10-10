import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactWeakConvergence

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactWeightedFiniteMeasure_apply_eq {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0))
    (s : Set (Ambient d)) (hs : MeasurableSet s) (hf : ∀ x ∈ s, f x = 1) :
    (compactWeightedFiniteMeasure μ f : Measure (Ambient d)) s = μ s := by
  have h := congrArg (fun ρ : Measure (Ambient d) => ρ univ)
    (compactWeightedFiniteMeasure_restrict μ f s hs hf)
  simpa using! h

theorem compactTestConvergence_support_tube {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν)
    (q : Ambient d → ℝ) (K : ℝ≥0) (hq : LipschitzWith K q)
    (hzero : ∀ᵐ x ∂ν, q x = 0) (a : Ambient d) (R ε r c : ℝ)
    (hε : 0 < ε) (hc : 0 < c) (hr : (K : ℝ) * r ≤ ε / 2)
    (hball : ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → c ≤ (μ j).real (ball x r)) :
    ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → q x < ε := by
  obtain ⟨f, hf, _⟩ := exists_compact_nonneg_cutoff (closedBall a (R + r))
    (isCompact_closedBall a (R + r))
  let νf := compactWeightedFiniteMeasure ν f
  let μf := fun j => compactWeightedFiniteMeasure (μ j) f
  let bad : Set (Ambient d) := {x | ε / 2 ≤ q x}
  have hclosed : IsClosed bad := isClosed_le continuous_const hq.continuous
  have hzero' : ∀ᵐ x ∂(νf : Measure (Ambient d)), q x = 0 :=
    (withDensity_absolutelyContinuous ν (fun x => (f x : ℝ≥0∞))).ae_le hzero
  have hbad : (νf : Measure (Ambient d)) bad = 0 := by
    have hnot : ∀ᵐ x ∂(νf : Measure (Ambient d)), x ∉ bad := by
      filter_upwards [hzero'] with x hx
      change ¬ ε / 2 ≤ q x
      rw [hx]
      linarith
    simpa only [ae_iff, not_not] using! hnot
  have hfront : (νf : Measure (Ambient d)) (frontier bad) = 0 :=
    measure_mono_null hclosed.frontier_subset hbad
  have hmass : Tendsto (fun j => (μf j : Measure (Ambient d)).real bad) atTop (𝓝 0) := by
    simpa only [Measure.real, hbad, ENNReal.toReal_zero] using!
      finiteMeasure_continuitySet_mass_tendsto μf νf
        (compactWeightedFiniteMeasure_tendsto μ ν hlocal f) bad hfront
  filter_upwards [hball, hmass.eventually (gt_mem_nhds hc)] with j hj hsmall
  intro x hx hxsupport
  by_contra hlarge
  have hlarge' : ε ≤ q x := le_of_not_gt hlarge
  have hsub : ball x r ⊆ bad := by
    intro y hy
    have hd : dist x y ≤ r := by
      simpa only [dist_comm] using! (show dist y x < r from hy).le
    have hdiff : q x - q y ≤ (K : ℝ) * dist x y := by
      have h := hq.dist_le_mul x y
      rw [Real.dist_eq] at h
      exact (le_abs_self _).trans h
    have hmul := mul_le_mul_of_nonneg_left hd K.coe_nonneg
    change ε / 2 ≤ q y
    linarith
  have hfone : ∀ y ∈ ball x r, f y = 1 := by
    intro y hy
    apply hf y
    apply mem_closedBall.mpr
    have hd := dist_triangle y x a
    have hy' : dist y x < r := hy
    have hx' : dist x a < R := hx
    linarith
  have heq : (μf j : Measure (Ambient d)).real (ball x r) = (μ j).real (ball x r) := by
    unfold Measure.real
    rw [show (μf j : Measure (Ambient d)) (ball x r) = (μ j) (ball x r) from
      compactWeightedFiniteMeasure_apply_eq (μ j) f (ball x r) measurableSet_ball hfone]
  have hmassge : c ≤ (μf j : Measure (Ambient d)).real bad := by
    calc
      c ≤ (μ j).real (ball x r) := hj x hx hxsupport
      _ = (μf j : Measure (Ambient d)).real (ball x r) := heq.symm
      _ ≤ _ := measureReal_mono hsub
  exact (not_lt_of_ge hmassge) hsmall

theorem compactTestConvergence_measure_tube {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν)
    (q : Ambient d → ℝ) (K : ℝ≥0) (hq : LipschitzWith K q)
    (hzero : ∀ᵐ x ∂ν, q x = 0) (a : Ambient d) (R ε r c : ℝ)
    (hε : 0 < ε) (hc : 0 < c) (hr : (K : ℝ) * r ≤ ε / 2)
    (hball : ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → c ≤ (μ j).real (ball x r)) :
    ∀ᶠ j in atTop, ∀ᵐ x ∂(μ j).restrict (ball a R), q x < ε := by
  filter_upwards [compactTestConvergence_support_tube μ ν hlocal q K hq hzero
    a R ε r c hε hc hr hball] with j hj
  filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae (μ j).support_mem_ae]
    with x hx hxsupport
  exact hj x hx hxsupport

theorem compactTestConvergence_dyadic_tubes {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν)
    (q : Ambient d → ℝ) (K : ℝ≥0) (hq : LipschitzWith K q)
    (hzero : ∀ᵐ x ∂ν, q x = 0) (a : Ambient d) (R : ℝ)
    (hball : ∀ r : ℝ, 0 < r → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → c ≤ (μ j).real (ball x r)) :
    ∀ k : ℕ, ∀ᶠ j in atTop, ∀ᵐ x ∂(μ j).restrict (ball a R), q x ≤ (1 / 2 : ℝ) ^ k := by
  intro k
  let ε : ℝ := (1 / 2 : ℝ) ^ k
  have hε : 0 < ε := by positivity
  let r : ℝ := ε / (2 * ((K : ℝ) + 1))
  have hr0 : 0 < r := by positivity
  obtain ⟨c, hc, hbc⟩ := hball r hr0
  have hr : (K : ℝ) * r ≤ ε / 2 := by
    dsimp [r]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hden : 0 < 2 * ((K : ℝ) + 1) := by positivity
    have heq : ε / (2 * ((K : ℝ) + 1)) * (2 * ((K : ℝ) + 1)) = ε :=
      div_mul_cancel₀ ε hden.ne'
    nlinarith [le_of_lt hr0]
  filter_upwards [compactTestConvergence_measure_tube μ ν hlocal q K hq hzero
    a R ε r c hε hc hr hbc] with j hj
  exact hj.mono fun _ hx => hx.le

end

end RieszRectifiability

end OAI
