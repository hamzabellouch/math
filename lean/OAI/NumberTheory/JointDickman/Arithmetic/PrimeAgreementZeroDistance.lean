import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDistanceComparison
import OAI.NumberTheory.JointDickman.Arithmetic.MertensDischarge
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

namespace OAI

/-! # Bounded zero-frequency distance from small-prime agreement -/
namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

lemma zeta_prime_distance_zero (X : ℝ) :
    primeDistanceSquared (ArithmeticFunction.zeta : ArithmeticFunction ℂ) X 0 = 0 := by
  unfold primeDistanceSquared
  apply sum_eq_zero
  intro p hp
  have hp0 := (mem_filter.mp hp).2.ne_zero
  simp [ArithmeticFunction.zeta_apply, hp0]

/-- A function equal to one at all small primes has bounded distance to
one, even after arbitrary fixed finite-prime changes. -/
theorem prime_agreement_zero_distance_bounded {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (P : Finset ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ X : ℝ in atTop, ∀ f : ArithmeticFunction ℂ,
      (∀ n, ‖f n‖ ≤ 1) →
      (∀ p : ℕ, p.Prime → p ∉ P → (p:ℝ) ≤ X^c → f p = 1) →
      primeDistanceSquared f X 0 ≤ C := by
  let C := 2*(-Real.log c+1+∑ p ∈ P, 1/(p:ℝ))
  have hcLog : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have hC : 0 ≤ C := by
    have hs : 0 ≤ ∑ p ∈ P, 1/(p:ℝ) := sum_nonneg (fun p _ => by positivity)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  have htail := (largePrimeSet_reciprocal_tendsto primeReciprocalMertensInput hc hc1).eventually
    (eventually_le_nhds (lt_add_one (-Real.log c)))
  filter_upwards [htail] with X hX
  intro f hf heq
  have hz : ∀ n : ℕ, ‖(ArithmeticFunction.zeta : ArithmeticFunction ℂ) n‖ ≤ 1 := by
    intro n
    by_cases hn : n=0 <;> simp [ArithmeticFunction.zeta_apply, hn]
  have hh := primeDistanceSquared_lower_of_agree
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) f hz hf P X (X^c) 0 (by
      intro p hp hpP hpX
      rw [heq p hp hpP hpX]
      simp [ArithmeticFunction.zeta_apply,hp.ne_zero])
  rw [zeta_prime_distance_zero] at hh
  dsimp [C]
  linarith

end JointDickman

end OAI
