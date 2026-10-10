import OAI.NumberTheory.TwoPointCorrelations.ResidueBox

namespace OAI

/-! Exact local density of the four rough-sieve forms. All coefficients
needed to solve pairs are units already over every nonzero modulus;
there is no exceptional argument at the prime two. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def zeroResidueIndicator {D : ℕ} [NeZero D] (x : ZMod D) : ℝ :=
  if x = 0 then 1 else 0

def fourFormBad {D : ℕ} [NeZero D] (x : ZMod D × ZMod D × ZMod D) : Prop :=
  x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0 ∨ x.1 + x.2.1 - x.2.2 = 0

lemma fourFormBad_indicator {D : ℕ} [NeZero D] (x y z : ZMod D) :
    (if fourFormBad (x, y, z) then (1 : ℝ) else 0) =
      zeroResidueIndicator x + zeroResidueIndicator y + zeroResidueIndicator z +
      zeroResidueIndicator (x + y - z) -
      (zeroResidueIndicator x * zeroResidueIndicator y +
        zeroResidueIndicator x * zeroResidueIndicator z +
        zeroResidueIndicator x * zeroResidueIndicator (x + y - z) +
        zeroResidueIndicator y * zeroResidueIndicator z +
        zeroResidueIndicator y * zeroResidueIndicator (x + y - z) +
        zeroResidueIndicator z * zeroResidueIndicator (x + y - z)) +
      (zeroResidueIndicator x * zeroResidueIndicator y * zeroResidueIndicator z +
        zeroResidueIndicator x * zeroResidueIndicator y *
          zeroResidueIndicator (x + y - z) +
        zeroResidueIndicator x * zeroResidueIndicator z *
          zeroResidueIndicator (x + y - z) +
        zeroResidueIndicator y * zeroResidueIndicator z *
          zeroResidueIndicator (x + y - z)) -
      zeroResidueIndicator x * zeroResidueIndicator y * zeroResidueIndicator z *
        zeroResidueIndicator (x + y - z) := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> by_cases hz : z = 0 <;>
    by_cases hw : x + y - z = 0 <;>
    simp only [fourFormBad, zeroResidueIndicator, hx, hy, hz, hw,
      ite_true, ite_false, true_or, false_or, or_true, or_false] <;> norm_num <;> ring

private lemma add_zero_iff_right {D : ℕ} [NeZero D] (x y : ZMod D) :
    x + y = 0 ↔ y = -x := by
  constructor
  · intro h
    calc
      y = (x + y) - x := by ring
      _ = -x := by rw [h]; ring
  · intro h
    rw [h]
    ring

/-- The count is exact for every nonzero modulus, not only prime moduli. -/
lemma fourFormBad_count (D : ℕ) [NeZero D] :
    (∑ x : ZMod D, ∑ y : ZMod D, ∑ z : ZMod D,
      if fourFormBad (x, y, z) then (1 : ℝ) else 0) =
        4 * (D : ℝ) ^ 2 - 6 * D + 3 := by
  simp only [fourFormBad_indicator, sum_add_distrib, sum_sub_distrib]
  simp [zeroResidueIndicator, mul_ite, sub_eq_zero,
    add_zero_iff_right, nsmul_eq_mul, ZMod.card]
  ring

lemma uniformResidueCube_probability {D : ℕ} [NeZero D]
    (E : (ZMod D × ZMod D × ZMod D) → Prop) :
    (uniformResidueCubeLaw D).probability E =
      (∑ x : ZMod D, ∑ y : ZMod D, ∑ z : ZMod D,
        if E (x, y, z) then (1 : ℝ) else 0) / (D : ℝ) ^ 3 := by
  unfold FiniteLaw.probability FiniteLaw.average uniformResidueCubeLaw
    FiniteLaw.product uniformZModLaw
  simp only [Fintype.sum_prod_type]
  simp_rw [← mul_assoc, ← mul_sum]
  ring

noncomputable def fourFormBadDensity (D : ℕ) [NeZero D] : ℝ :=
  (uniformResidueCubeLaw D).probability fourFormBad

theorem fourFormBadDensity_exact (D : ℕ) [NeZero D] :
    fourFormBadDensity D = (4 * (D : ℝ) ^ 2 - 6 * D + 3) / (D : ℝ) ^ 3 := by
  rw [fourFormBadDensity, uniformResidueCube_probability, fourFormBad_count]

lemma fourFormBadDensity_nonneg (D : ℕ) [NeZero D] : 0 ≤ fourFormBadDensity D :=
  (uniformResidueCubeLaw D).probability_nonneg fourFormBad

theorem fourFormBadDensity_bounds (D : ℕ) [NeZero D] :
    4 / (D : ℝ) - 6 / (D : ℝ) ^ 2 ≤ fourFormBadDensity D ∧
      fourFormBadDensity D ≤ 4 / (D : ℝ) := by
  have hD : (0 : ℝ) < D := by exact_mod_cast NeZero.pos D
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast NeZero.pos D
  rw [fourFormBadDensity_exact]
  constructor
  · apply (le_div_iff₀ (pow_pos hD 3)).mpr
    field_simp
    nlinarith
  · apply (div_le_iff₀ (pow_pos hD 3)).mpr
    field_simp
    nlinarith

theorem fourFormBadDensity_lt_one (D : ℕ) [NeZero D] (hD : 2 ≤ D) :
    fourFormBadDensity D < 1 := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast NeZero.pos D
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  rw [fourFormBadDensity_exact, div_lt_one (pow_pos hDr 3)]
  have hprod : 0 < ((D : ℝ) - 1) * (((D : ℝ) - 1) * ((D : ℝ) - 2) + 1) := by
    apply mul_pos (by linarith)
    have : 0 ≤ ((D : ℝ) - 1) * ((D : ℝ) - 2) := mul_nonneg (by linarith) (by linarith)
    linarith
  nlinarith

lemma oneFormBadDensity (D : ℕ) [NeZero D] :
    (uniformZModLaw D).probability (fun x => x = 0) = 1 / (D : ℝ) := by
  simp [FiniteLaw.probability, FiniteLaw.average, uniformZModLaw]

end TwoPointCorrelations

end OAI
