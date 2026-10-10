import OAI.NumberTheory.JointDickman.Amplification.AmplificationFirstForm
import OAI.NumberTheory.JointDickman.Amplification.BinLabels

namespace OAI

/-! # The first form for actual large-prime bin labels -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem binLabel_auxiliary_multipliers {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (B : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ A ∈ (auxiliaryPrimes B).powerset, ∀ m : ℕ,
      binLabel (fun i => primeBin x J (k i)) z ((∏ p ∈ A, p)*m) =
        binLabel (fun i => primeBin x J (k i)) z m := by
  apply (eventually_all_finset (auxiliaryPrimes B).powerset).mpr
  intro A hA
  have ha : 0 < ∏ p ∈ A, p := prod_pos (fun p hp =>
    (auxiliaryPrimes_prime B p (mem_powerset.mp hA hp)).pos)
  exact binLabel_eventually_mul_invariant J hJ k hk z (ne_of_gt ha)

/-- The exact normalized first-form identity holds at all sufficiently
large integer scales; no multiplicativity of the centered second factor
is used. -/
theorem binLabel_amplification_first_form {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i) (z : ι → ℂ)
    (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (H : ℕ → ℕ → ℂ) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, (star (binLabel (fun i => primeBin (N : ℝ) J (k i)) z n) * H N n) *
        (arithmeticSubsetAmplification B L τ C (fun a c => u c * v a c) n : ℂ)) / (N : ℂ) =
      (1 / (B : ℂ)) * firstDivisorForm B L τ C u v
        (binLabel (fun i => primeBin (N : ℝ) J (k i)) z) (H N) N := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (binLabel_auxiliary_multipliers J hJ k hk z B)] with N hN
  rw [arithmeticAmplification_reindex]
  have h := amplification_first_form B L τ C u v
    (binLabel (fun i => primeBin (N : ℝ) J (k i)) z) (H N) N hN
  rw [mul_div_assoc, h]

end JointDickman

end OAI
