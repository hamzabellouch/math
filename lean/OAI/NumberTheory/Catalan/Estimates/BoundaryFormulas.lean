import OAI.NumberTheory.Catalan.Polynomial.CentralCoefficients

namespace OAI


namespace InternalCatalan

open scoped BigOperators

def parityBoundarySum (f : ℕ → ℚ) (u : ℕ) : ℚ :=
  ∑ z ∈ Finset.range (u + 1), if 0 < z ∧ z % 2 = u % 2 then f z else 0

@[simp] theorem parityBoundarySum_zero (f : ℕ → ℚ) : parityBoundarySum f 0 = 0 := by
  simp [parityBoundarySum]

@[simp] theorem parityBoundarySum_one (f : ℕ → ℚ) : parityBoundarySum f 1 = f 1 := by
  simp [parityBoundarySum, Finset.sum_range_succ]

theorem parityBoundarySum_step (f : ℕ → ℚ) (u : ℕ) :
    parityBoundarySum f (u + 2) = parityBoundarySum f u + f (u + 2) := by
  have hp : (u + 2) % 2 = u % 2 := by omega
  have hn : ¬(0 < u + 1 ∧ (u + 1) % 2 = u % 2) := by omega
  have hn' : (u + 1) % 2 ≠ u % 2 := by omega
  have ht : 0 < u + 2 ∧ (u + 2) % 2 = u % 2 := by omega
  unfold parityBoundarySum
  simp_rw [hp]
  rw [show u + 2 + 1 = (u + 1) + 1 + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]
  simp [hn', ht]

def boundaryPlusWeight (z : ℕ) : ℚ := 2 / ((z : ℚ) ^ 2 * boundaryFactor z)

theorem boundaryPlus_explicit (u : ℕ) :
    boundaryPlus (u + 1) = boundaryFactor u * parityBoundarySum boundaryPlusWeight u := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    cases u with
    | zero => simp
    | succ u =>
      cases u with
      | zero => norm_num [boundaryPlus, boundaryPlusWeight]
      | succ u =>
        change boundaryPlus (u + 2 + 1) =
          boundaryFactor (u + 2) * parityBoundarySum boundaryPlusWeight (u + 2)
        have hs := boundaryFactor_step u
        have hu : ((u + 2 : ℕ) : ℚ) ≠ 0 := by positivity
        have hf := boundaryFactor_ne_zero (u + 2)
        have hu1 : ((u + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        have hf0 := boundaryFactor_ne_zero u
        have hr : boundaryFactor (u + 2) =
            ((u + 1 : ℕ) : ℚ) * boundaryFactor u / ((u + 2 : ℕ) : ℚ) := by
          apply (eq_div_iff hu).2
          simpa [mul_comm] using hs
        rw [show u + 2 + 1 = (u + 1) + 2 by omega, boundaryPlus,
          ih u (by omega), parityBoundarySum_step]
        unfold boundaryPlusWeight
        rw [hr]
        field_simp

def boundaryMinusWeight (z : ℕ) : ℚ :=
  if z % 2 = 0 then 2 / ((z : ℚ) ^ 2 * boundaryFactor z ^ 2)
  else 2 / (z : ℚ)

theorem boundaryMinus_increment (d : ℕ) :
    (momentScalar d + momentScalar (d + 1)) /
        (((d + 2 : ℕ) : ℚ) * boundaryFactor (d + 2)) =
      boundaryMinusWeight (d + 2) := by
  by_cases hd : d % 2 = 0
  · have heq : d = 2 * (d / 2) := by omega
    generalize d / 2 = l at heq
    subst d
    rw [momentScalar_even, momentScalar_odd]
    rw [show 2 * l + 2 = 2 * (l + 1) by omega]
    have hp : (2 * (l + 1)) % 2 = 0 := by omega
    rw [boundaryMinusWeight, ite_eq_left hp]
    simp only [boundaryFactor_even, add_zero]
    have hc : ((2 * l + 1 : ℕ) : ℚ) * centralCoeff l =
        ((2 * (l + 1) : ℕ) : ℚ) * centralCoeff (l + 1) := by
      exact (centralCoeff_step l).symm
    rw [hc]
    have hden : ((2 * (l + 1) : ℕ) : ℚ) ≠ 0 := by positivity
    have hfactor := centralCoeff_ne_zero (l + 1)
    field_simp
  · have heq : d = 2 * (d / 2) + 1 := by omega
    generalize d / 2 = l at heq
    subst d
    rw [momentScalar_odd,
      show 2 * l + 1 + 1 = 2 * (l + 1) by omega, momentScalar_even,
      show 2 * l + 1 + 2 = 2 * (l + 1) + 1 by omega]
    have hp : (2 * (l + 1) + 1) % 2 ≠ 0 := by omega
    simp only [boundaryMinusWeight, ite_eq_right hp, boundaryFactor_odd, zero_add]
    have hden : ((2 * (l + 1) + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hfactor := centralCoeff_ne_zero (l + 1)
    field_simp

theorem boundaryMinus_explicit (u : ℕ) :
    boundaryMinus u = boundaryFactor u * parityBoundarySum boundaryMinusWeight u := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    cases u with
    | zero => simp
    | succ u =>
      cases u with
      | zero => norm_num [boundaryMinusWeight]
      | succ u =>
        change boundaryMinus (u + 2) =
          boundaryFactor (u + 2) * parityBoundarySum boundaryMinusWeight (u + 2)
        have hu : ((u + 2 : ℕ) : ℚ) ≠ 0 := by positivity
        have hf := boundaryFactor_ne_zero (u + 2)
        have hs := boundaryFactor_step u
        have hw := boundaryMinus_increment u
        have hr : ((u + 1 : ℕ) : ℚ) * boundaryFactor u =
            ((u + 2 : ℕ) : ℚ) * boundaryFactor (u + 2) := hs.symm
        have hw' : momentScalar u + momentScalar (u + 1) =
            boundaryMinusWeight (u + 2) *
              (((u + 2 : ℕ) : ℚ) * boundaryFactor (u + 2)) :=
          (div_eq_iff (mul_ne_zero hu hf)).mp hw
        rw [boundaryMinus, ih u (by omega), parityBoundarySum_step]
        rw [show ((u + 1 : ℕ) : ℚ) *
              (boundaryFactor u * parityBoundarySum boundaryMinusWeight u) =
            (((u + 1 : ℕ) : ℚ) * boundaryFactor u) *
              parityBoundarySum boundaryMinusWeight u by ring, hr]
        rw [show ((u + 2 : ℕ) : ℚ) * boundaryFactor (u + 2) *
                parityBoundarySum boundaryMinusWeight u + momentScalar u + momentScalar (u + 1) =
              ((u + 2 : ℕ) : ℚ) * boundaryFactor (u + 2) *
                parityBoundarySum boundaryMinusWeight u +
                  (momentScalar u + momentScalar (u + 1)) by ring, hw']
        field_simp

end InternalCatalan

end OAI
