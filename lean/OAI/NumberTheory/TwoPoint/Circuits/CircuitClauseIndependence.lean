import OAI.NumberTheory.TwoPoint.Circuits.CircuitComparison

namespace OAI

/-! The first gate case of bounded-independence circuit fooling. A clause is
the complement of a Boolean cylinder. Restricting a wide clause to t distinct
coordinates makes both its exceptional probabilities at most 2⁻ᵗ. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {n : ℕ}

lemma cubeAverage_pattern (S : Finset (Fin n)) (z : BooleanCube n) :
    cubeAverage (cubePattern S z) = 1 / (2 : ℝ) ^ S.card := by
  have hm : cubeAverage (fun _ : BooleanCube n => (1 : ℝ)) = 1 := cubeAverage_const 1
  have hc : ∀ T ⊆ S, T.Nonempty → walshCoefficient (fun _ => (1 : ℝ)) T = 0 := by
    intro T _ hT
    simpa only [walshCoefficient, one_mul] using cubeAverage_walsh hT
  simpa only [one_mul] using cubeAverage_pattern_of_walsh (fun _ => 1) S z hm hc

lemma cubePattern_nonneg (S : Finset (Fin n)) (z x : BooleanCube n) :
    0 ≤ cubePattern S z x := by
  unfold cubePattern
  split_ifs <;> norm_num

lemma cubePattern_antitone {S T : Finset (Fin n)} (hTS : T ⊆ S)
    (z x : BooleanCube n) : cubePattern S z x ≤ cubePattern T z x := by
  unfold cubePattern
  by_cases hS : ∀ i ∈ S, x i = z i
  · have hT : ∀ i ∈ T, x i = z i := fun i hi => hS i (hTS hi)
    rw [ite_eq_left hS, ite_eq_left hT]
  · rw [ite_eq_right hS]
    split_ifs <;> norm_num

/-- Exact t-wise independence bounds a cylinder of at least t coordinates,
even when the cylinder uses more than t coordinates. -/
lemma TWiseUniformDensity.large_pattern_bound {n t : ℕ} {g : BooleanCube n → ℝ}
    (hg : TWiseUniformDensity g t) (hn : ∀ x, 0 ≤ g x)
    (S : Finset (Fin n)) (ht : t ≤ S.card) (z : BooleanCube n) :
    0 ≤ cubeAverage (fun x => g x * cubePattern S z x) ∧
      cubeAverage (fun x => g x * cubePattern S z x) ≤ 1 / (2 : ℝ) ^ t := by
  obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq ht
  refine ⟨?_, ?_⟩
  · have hh := cubeAverage_mono (fun x => mul_nonneg (hn x) (cubePattern_nonneg S z x))
    simpa only [cubeAverage_const] using hh
  · calc
      cubeAverage (fun x => g x * cubePattern S z x) ≤
          cubeAverage (fun x => g x * cubePattern T z x) :=
        cubeAverage_mono (fun x => mul_le_mul_of_nonneg_left
          (cubePattern_antitone hTS z x) (hn x))
      _ = 1 / (2 : ℝ) ^ t := by rw [hg T (by omega) z, hT]

/-- A clause, represented as the complement of its unique failing pattern,
is fooled to error 2⁻ᵗ, independently of its width. -/
theorem TWiseUniformDensity.clause_error {n t : ℕ} {g : BooleanCube n → ℝ}
    (hg : TWiseUniformDensity g t) (hn : ∀ x, 0 ≤ g x)
    (hm : cubeAverage g = 1) (S : Finset (Fin n)) (z : BooleanCube n) :
    |cubeAverage (fun x => g x * (1 - cubePattern S z x)) -
      cubeAverage (fun x => 1 - cubePattern S z x)| ≤ 1 / (2 : ℝ) ^ t := by
  have heq : cubeAverage (fun x => g x * (1 - cubePattern S z x)) -
      cubeAverage (fun x => 1 - cubePattern S z x) =
      cubeAverage (cubePattern S z) - cubeAverage (fun x => g x * cubePattern S z x) := by
    simp_rw [mul_sub, mul_one]
    rw [cubeAverage_sub, cubeAverage_sub, hm, cubeAverage_const]
    ring
  rw [heq]
  by_cases hS : S.card ≤ t
  · rw [hg S hS z, cubeAverage_pattern, sub_self, abs_zero]
    positivity
  · have hlarge := hg.large_pattern_bound hn S (by omega) z
    have hsmall : 0 ≤ cubeAverage (cubePattern S z) := by
      rw [cubeAverage_pattern]
      positivity
    have hbound : cubeAverage (cubePattern S z) ≤ 1 / (2 : ℝ) ^ t := by
      rw [cubeAverage_pattern]
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact abs_le.mpr ⟨by linarith [hlarge.2], by linarith [hlarge.1]⟩

end TwoPointCorrelations

end OAI
