import Mathlib.Analysis.MeanInequalitiesPow
import OAI.NumberTheory.Ostmann.Characters.BonamiTwoPoint

namespace OAI

/-! # Finite moment interpolation for the Boolean-cube induction -/

namespace Ostmann

open Finset
open scoped BigOperators

private theorem sum_add_pow_bound_pos {ι : Type*} (s : Finset ι)
    (u v : ι → ℝ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i) (l : ℕ)
    (hU : (∑ i ∈ s, u i ^ l) ≤ s.card * A ^ l)
    (hV : (∑ i ∈ s, v i ^ l) ≤ s.card * B ^ l) :
    (∑ i ∈ s, (u i + v i) ^ l) ≤ s.card * (A + B) ^ l := by
  have hAB : 0 < A + B := add_pos hA hB
  have hweights : A / (A + B) + B / (A + B) = 1 := by field_simp
  have hpoint (i : ι) (hi : i ∈ s) :
      ((u i + v i) / (A + B)) ^ l ≤
        A / (A + B) * (u i / A) ^ l + B / (A + B) * (v i / B) ^ l := by
    have h := (convexOn_pow l).2 (div_nonneg (hu i hi) hA.le)
      (div_nonneg (hv i hi) hB.le)
      (div_nonneg hA.le hAB.le) (div_nonneg hB.le hAB.le) hweights
    dsimp only [smul_eq_mul] at h
    convert h using 1
    congr 1
    field_simp
  have hsum : (∑ i ∈ s, (u i + v i) ^ l) / (A + B) ^ l ≤
      A / (A + B) * ((∑ i ∈ s, u i ^ l) / A ^ l) +
        B / (A + B) * ((∑ i ∈ s, v i ^ l) / B ^ l) := by
    calc
      _ = ∑ i ∈ s, ((u i + v i) / (A + B)) ^ l := by
        simp only [div_pow, sum_div]
      _ ≤ ∑ i ∈ s, (A / (A + B) * (u i / A) ^ l +
          B / (A + B) * (v i / B) ^ l) := sum_le_sum hpoint
      _ = _ := by simp only [div_pow, sum_add_distrib, ← mul_sum, sum_div]
  have hUA : (∑ i ∈ s, u i ^ l) / A ^ l ≤ s.card :=
    (div_le_iff₀ (pow_pos hA l)).mpr hU
  have hVB : (∑ i ∈ s, v i ^ l) / B ^ l ≤ s.card :=
    (div_le_iff₀ (pow_pos hB l)).mpr hV
  apply (div_le_iff₀ (pow_pos hAB l)).mp
  calc
    _ ≤ A / (A + B) * ((∑ i ∈ s, u i ^ l) / A ^ l) +
        B / (A + B) * ((∑ i ∈ s, v i ^ l) / B ^ l) := hsum
    _ ≤ A / (A + B) * s.card + B / (A + B) * s.card := by
      exact add_le_add (mul_le_mul_of_nonneg_left hUA (div_nonneg hA.le hAB.le))
        (mul_le_mul_of_nonneg_left hVB (div_nonneg hB.le hAB.le))
    _ = s.card := by rw [← add_mul, hweights, one_mul]

private theorem eq_zero_of_sum_pow_le_zero {ι : Type*} (s : Finset ι)
    (u : ι → ℝ) (hu : ∀ i ∈ s, 0 ≤ u i) (l : ℕ)
    (hU : (∑ i ∈ s, u i ^ l) ≤ 0) : ∀ i ∈ s, u i = 0 := by
  intro i hi
  have hterm := (single_le_sum (fun j hj => pow_nonneg (hu j hj) l) hi).trans hU
  by_contra hn
  exact (not_le_of_gt (pow_pos (lt_of_le_of_ne (hu i hi) (Ne.symm hn)) l)) hterm

/-- The finite-sum form needed for tensorization, with no analytic limits. -/
theorem sum_add_pow_bound {ι : Type*} (s : Finset ι)
    (u v : ι → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i) (l : ℕ) (hl : 0 < l)
    (hU : (∑ i ∈ s, u i ^ l) ≤ s.card * A ^ l)
    (hV : (∑ i ∈ s, v i ^ l) ≤ s.card * B ^ l) :
    (∑ i ∈ s, (u i + v i) ^ l) ≤ s.card * (A + B) ^ l := by
  rcases eq_or_lt_of_le hA with hA | hA
  · subst A
    have hzero : ∀ i ∈ s, u i = 0 := eq_zero_of_sum_pow_le_zero s u hu l (by
      simpa only [zero_pow (Nat.ne_of_gt hl), mul_zero] using hU)
    have hid : (∑ i ∈ s, (u i + v i) ^ l) = ∑ i ∈ s, v i ^ l := by
      apply sum_congr rfl
      intro i hi
      rw [hzero i hi, zero_add]
    rw [hid, zero_add]
    exact hV
  rcases eq_or_lt_of_le hB with hB | hB
  · subst B
    have hzero : ∀ i ∈ s, v i = 0 := eq_zero_of_sum_pow_le_zero s v hv l (by
      simpa only [zero_pow (Nat.ne_of_gt hl), mul_zero] using hV)
    have hid : (∑ i ∈ s, (u i + v i) ^ l) = ∑ i ∈ s, u i ^ l := by
      apply sum_congr rfl
      intro i hi
      rw [hzero i hi, add_zero]
    rw [hid, add_zero]
    exact hU
  exact sum_add_pow_bound_pos s u v A B hA hB hu hv l hU hV

end Ostmann

end OAI
