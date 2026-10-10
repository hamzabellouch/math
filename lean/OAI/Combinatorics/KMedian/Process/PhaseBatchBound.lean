import Mathlib
import OAI.Combinatorics.KMedian.Geometry.PotentialBounds
import OAI.Combinatorics.KMedian.Process.PhysicalBatchLaw
import OAI.Combinatorics.KMedian.Geometry.FixedBatchTransition
import OAI.Combinatorics.KMedian.Geometry.TimeAdvance

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential
open Analytic
variable {I Ω : Type*} [DecidableEq I] [Fintype Ω]

theorem expected_time_advance (μ : FiniteLaw Ω) (S' : Ω → Finset I) (b' : Ω → ℝ)
    {x g R h : ℝ} (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R) (hh : 0 ≤ h)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hsub : ∀ ω, S' ω ⊆ S) :
    μ.expect (fun ω => potential (x*Real.exp (-h)) g d (S' ω) (b' ω)-
      potential x g d (S' ω) (b' ω)) ≤
      h*timeRate x (mass g S)*cost g d S+6*h^2*R+
        4*h*R*μ.prob (fun ω => S' ω ≠ S) := by
  have hV0 := cost_nonneg hg hd0
  have hVR := cost_le_radius hg hR hdR hy
  have rate_bound : ∀ T ⊆ S, |timeRate x (mass g T)*cost g d T| ≤ 2*R := by
    intro T hT
    have hV := cost_nonneg hg (fun i hi => hd0 i (hT hi))
    rw [abs_mul, abs_of_nonneg hV]
    exact mul_le_mul (abs_timeRate hx0 hx1 (mass_nonneg hg T) ((mass_mono hg hT).trans hy))
      (cost_le_radius hg hR (fun i hi => hdR i (hT hi)) ((mass_mono hg hT).trans hy))
      hV (by norm_num)
  have hp : ∀ ω, potential (x*Real.exp (-h)) g d (S' ω) (b' ω)-
      potential x g d (S' ω) (b' ω) ≤
      h*timeRate x (mass g S)*cost g d S+6*h^2*R+
        4*h*R*(if S' ω ≠ S then 1 else 0) := by
    intro ω
    have he := potential_time_error (b := b' ω) hx0 hx1 hg
      (fun i hi => hd0 i (hsub ω hi)) ((mass_mono hg (hsub ω)).trans hy) hh
    have he' := (le_abs_self _).trans he
    have hnew := cost_le_radius hg hR (fun i hi => hdR i (hsub ω hi))
      ((mass_mono hg (hsub ω)).trans hy)
    have hbound := mul_le_mul_of_nonneg_left hnew (by positivity : 0 ≤ 6*h^2)
    by_cases hs : S' ω = S
    · simp only [hs, ne_eq, not_true_eq_false, ite_false, mul_zero, add_zero] at he' hbound ⊢
      linarith only [he', hbound]
    · have hdiff := sub_le_sub ((abs_le.mp (rate_bound (S' ω) (hsub ω))).2)
        ((abs_le.mp (rate_bound S (by rfl))).1)
      have hmul := mul_le_mul_of_nonneg_left hdiff hh
      simp only [hs, ne_eq, not_false_eq_true, ite_true, mul_one]
      nlinarith only [he', hbound, hmul]
  have he := μ.expect_mono hp
  simpa only [FiniteLaw.expect_add, FiniteLaw.expect_const, FiniteLaw.expect_mul,
    FiniteLaw.prob] using he

end MetricKMedian.PhysicalPotential

namespace MetricKMedian.PhysicalBatchLaw
open Finset
variable {E : Type*} [Fintype E] [DecidableEq E]
 theorem marginal_le (Z : Finset E) (C : E → Finset E)
    (p : ℝ) (q : E → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hself : ∀ e, e ∉ C e) {Q : ℝ} (hpQ : p ≤ Q) (hqQ : ∀ e, q e ≤ Q) (e : E) :
    (law Z C p q hp0 hp1 hq0 hq1).prob (fun A => e ∈ A) ≤ Q/2 := by
  rw [marginal Z C p q hp0 hp1 hq0 hq1 e (hself e)]
  split_ifs
  · have hpow : (1-p)^(C e).card ≤ 1 := pow_le_one₀ (by linarith only [hp1]) (by linarith only [hp0])
    have hm := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (1/2:ℝ)*p)
    linarith only [hm, hpQ]
  · linarith only [hqQ e]
end MetricKMedian.PhysicalBatchLaw

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
 theorem change_probability_le (D : Actions I E) (μ : FiniteLaw (Finset E))
    (x g : ℝ) (d : I → ℝ) (S : Finset I) {Q : ℝ}
    (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ Q) :
    μ.prob (fun A => nextAlive D x g d S A ≠ S) ≤ ((relevant D S).card:ℝ)*Q := by
  have hm := μ.prob_mono (E := fun A => nextAlive D x g d S A ≠ S)
    (F := fun A => ∃ e ∈ relevant D S, e ∈ A) (by
      intro A ha
      by_contra hn
      have hi : A ∩ relevant D S=∅ := eq_empty_iff_forall_notMem.mpr (by
        intro e he
        exact hn ⟨e, (mem_inter.mp he).2, (mem_inter.mp he).1⟩)
      exact ha (nextAlive_zero D x g d S A hi))
  have hu := μ.prob_exists_le_sum (relevant D S) (fun e A => e ∈ A)
  have hs := sum_le_sum hmarg
  simp only [sum_const, nsmul_eq_mul] at hs
  exact hm.trans (hu.trans hs)
end MetricKMedian.FixedBatch
end
end

end OAI
