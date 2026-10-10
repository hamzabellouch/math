import OAI.NumberTheory.JointDickman.Probability.ArithmeticMomentDecay
import OAI.NumberTheory.JointDickman.Counting.RealPeriodicMoments

namespace OAI

/-! # Bounded second moment of the actual divisor amplification -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem arithmeticAmplification_moment_tendsto (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, (arithmeticSubsetAmplification B L τ C w n)^k) / (N : ℝ))
      atTop (nhds (arithmeticAmplificationMoment B L τ C w k)) := by
  have h := real_periodic_moment_tendsto (q := auxiliarySquarePeriod B)
    (residueAmplification B L τ C w) k
  have he : (fun N : ℕ => (∑ n ∈ range N,
      (residueAmplification B L τ C w (n : ZMod (auxiliarySquarePeriod B)))^k) / (N : ℝ)) =
      (fun N : ℕ => (∑ n ∈ range N,
        (arithmeticSubsetAmplification B L τ C w n)^k) / (N : ℝ)) := by
    funext N
    congr 1
    apply sum_congr rfl
    intro n _
    rw [residueAmplification_natCast B L n τ C w]
  rw [he] at h
  exact h

theorem arithmeticAmplification_second_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∀ (L : ℕ) (τ C : ℝ), ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (T : ℕ) (w : ℕ → ℕ → ℝ), 0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) →
      (∀ a c, (a, c) ∉ amplificationCoefficientPairs B T → w a c = 0) →
      arithmeticAmplificationMoment B L τ C w 2 ≤ K := by
  intro L τ C
  obtain ⟨K, hK, hb⟩ := weightedAmplification_second_bound hFord hM L τ C
  have he := amplification_quadratic_error_tendsto.eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨K+1, by linarith, ?_⟩
  filter_upwards [hb, he, eventually_gt_atTop 1] with B hB hE hB1
  intro T w hT hTsize hw hsupp
  have hi : independentAmplificationMoment B L τ C w 2 ≤ K := hB T w hT hTsize hw hsupp
  have hc := arithmeticMoment_independent_error (L := L) (τ := τ) (C := C) hB1 w hw 2
  have hu := (le_abs_self _).trans (hc.trans hE)
  linarith

end JointDickman

end OAI
