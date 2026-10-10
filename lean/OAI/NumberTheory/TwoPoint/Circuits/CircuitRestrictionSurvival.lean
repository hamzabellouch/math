import OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionProbability
import OAI.NumberTheory.TwoPoint.Circuits.CircuitGateFailure

namespace OAI

/-! A Fourier support with sufficiently many expected live coordinates
retains more than `t` coordinates with probability at least one half. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma booleanCount_restrict {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    booleanCount (fun i : S => x i) = ((S ∩ sampledCoordinates x).card : ℝ) := by
  unfold booleanCount
  rw [sum_coe_sort S (fun i => if x i then (1 : ℝ) else 0)]
  have hset : S ∩ sampledCoordinates x = S.filter (fun i => x i = true) := by
    ext i
    simp [sampledCoordinates]
  rw [hset]
  exact sum_boole (fun i => x i = true) S

theorem bernoulli_support_survival {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (Fin n)) (t : ℕ)
    (ht : 2 * (t : ℝ) ≤ p * S.card) (hlarge : 8 ≤ p * S.card) :
    1 / 2 ≤ (bernoulliCubeLaw n p hp hp1).probability
      (fun x => t < (S ∩ sampledCoordinates x).card) := by
  have h := independent_boolean_survival (fun _ : S => p) (fun _ => hp) (fun _ => hp1)
    (t : ℝ) (by simpa [mul_comm] using ht) (by simpa [mul_comm] using hlarge)
  have heq : (bernoulliCubeLaw n p hp hp1).probability
      (fun x => t < (S ∩ sampledCoordinates x).card) =
      (FiniteLaw.independent (fun _ : S => booleanLaw p hp hp1)).probability
        (fun x => (t : ℝ) < booleanCount x) := by
    unfold FiniteLaw.probability
    refine Eq.trans ?_ (FiniteLaw.independent_average_restrict
      (fun _ : Fin n => booleanLaw p hp hp1) S
      (fun x => if (t : ℝ) < booleanCount x then (1 : ℝ) else 0))
    apply congrArg (bernoulliCubeLaw n p hp hp1).average
    funext x
    simp only [booleanCount_restrict, Nat.cast_lt]
    by_cases hx : t < (S ∩ sampledCoordinates x).card <;> simp [hx]
  rw [heq]
  exact h

end TwoPointCorrelations

end OAI
