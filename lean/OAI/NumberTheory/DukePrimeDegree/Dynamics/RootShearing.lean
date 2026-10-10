import OAI.NumberTheory.DukePrimeDegree.Dynamics.PublishedEKL

namespace OAI

/-!
# Polynomial shearing along a root subgroup

The exact matrix formula is the algebraic part of the low-entropy
argument: conjugation by a root unipotent is quadratic in its parameter.
The exceptional case is precisely the centralizer, and commuting with a
single nonzero root element already characterizes that case.
-/

open scoped BigOperators Classical
open Filter

namespace DukePrimeDegree

open PrimeDegreePackets

lemma root_left_mul_entry {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (r s : Fin n) (t : ℝ) :
    (Matrix.SpecialLinearGroup.transvection hij t * g).1 r s =
      g.1 r s + if r = i then t * g.1 j s else 0 := by
  change (Matrix.transvection i j t * g.1) r s = _
  by_cases h : r = i
  · subst r
    simp [Matrix.transvection_mul_apply_same]
  · simp [Matrix.transvection_mul_apply_of_ne, h]

/-- The quadratic root-shearing formula, for arbitrary matrix indices. -/
theorem root_conjugation_entry {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (r s : Fin n) (t : ℝ) :
    (Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s =
      g.1 r s + (if r = i then t * g.1 j s else 0) -
        (if s = j then t * g.1 r i else 0) -
        (if r = i ∧ s = j then t ^ 2 * g.1 j i else 0) := by
  rw [root_mul_entry, root_left_mul_entry, root_left_mul_entry]
  by_cases hr : r = i <;> by_cases hs : s = j
  all_goals simp only [hr, hs, ite_true, ite_false, true_and, false_and]
  all_goals ring

/-- A matrix centralizes the entire root group exactly when its pivot
column, pivot row and two diagonal entries satisfy these equations. -/
theorem commutes_root_one_iff {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) :
    g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g ↔
      (∀ r, r ≠ i → g.1 r i = 0) ∧
      (∀ s, s ≠ j → g.1 j s = 0) ∧ g.1 i i = g.1 j j := by
  constructor
  · intro h
    have he (r s : Fin n) := congrArg (fun a : G n => a.1 r s) h
    simp only [root_mul_entry, root_left_mul_entry, mul_one, one_mul] at he
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      have h := he r j
      simp only [ite_true, ite_eq_right hr] at h
      linarith
    · intro s hs
      have h := he i s
      simp only [ite_eq_right hs, ite_true] at h
      linarith
    · have h := he i j
      simp only [ite_true] at h
      linarith
  · rintro ⟨hcol, hrow, hdiag⟩
    ext r s
    simp only [root_mul_entry, root_left_mul_entry, mul_one, one_mul]
    by_cases hr : r = i <;> by_cases hs : s = j
    · subst r
      subst s
      simp only [ite_true, hdiag]
    · subst r
      simp [hs, hrow s hs]
    · subst s
      simp [hr, hcol r hr]
    · simp [hr, hs]

/-- The centralizer of a root element at parameter one is the
centralizer of the full real root subgroup. -/
theorem commutes_root_one_iff_all {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) :
    g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g ↔
      ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
        Matrix.SpecialLinearGroup.transvection hij t * g := by
  constructor
  · intro h t
    obtain ⟨hcol, hrow, hdiag⟩ := (commutes_root_one_iff hij g).mp h
    ext r s
    simp only [root_mul_entry, root_left_mul_entry]
    by_cases hr : r = i <;> by_cases hs : s = j
    · subst r
      subst s
      simp only [ite_true, hdiag, mul_comm]
    · subst r
      simp [hs, hrow s hs]
    · subst s
      simp [hr, hcol r hr]
    · simp [hr, hs]
  · exact fun h => h 1

/-- A quadratic polynomial bounded on the positive half-line is
constant. This version keeps the exact coefficients used in shearing. -/
lemma bounded_quadratic_constant (a b c B : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t → |a + b * t + c * t ^ 2| ≤ B) :
    ∀ t : ℝ, a + b * t + c * t ^ 2 = a := by
  let P : Polynomial ℝ := Polynomial.C a + Polynomial.C b * Polynomial.X +
    Polynomial.C c * Polynomial.X ^ 2
  have heval (t : ℝ) : P.eval t = a + b * t + c * t ^ 2 := by simp [P]
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun t : ℝ => |P.eval t|) := by
    refine ⟨B, eventually_map.mpr ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa only [heval] using hbound t ht
  have hdeg : P.degree ≤ 0 := (Polynomial.isBoundedUnder_abs_atTop_iff P).mp hb
  have hc := Polynomial.eq_C_of_degree_le_zero hdeg
  have hconst (t : ℝ) : P.eval t = P.eval 0 := by rw [hc]; simp
  intro t
  simpa only [heval, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using hconst t

/-- A root-conjugation trajectory stays bounded for all positive times
only in the exceptional, centralizing case. -/
theorem commutes_root_of_bounded_conjugation {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (g : G n) (B : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t → ∀ r s : Fin n,
      |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s| ≤ B) :
    ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g := by
  apply (commutes_root_one_iff_all hij g).mp
  have hconstant (t : ℝ) : Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t) = g := by
    ext r s
    let b : ℝ := (if r = i then g.1 j s else 0) -
      (if s = j then g.1 r i else 0)
    let c : ℝ := if r = i ∧ s = j then -g.1 j i else 0
    have hpoly (u : ℝ) :
        (Matrix.SpecialLinearGroup.transvection hij u * g *
          Matrix.SpecialLinearGroup.transvection hij (-u)).1 r s =
          g.1 r s + b * u + c * u ^ 2 := by
      rw [root_conjugation_entry]
      dsimp [b, c]
      split_ifs <;> ring
    rw [hpoly]
    apply bounded_quadratic_constant _ _ _ B ?_ t
    intro u hu
    rw [← hpoly]
    exact hbound u hu r s
  have hm := congrArg (fun h : G n => h * Matrix.SpecialLinearGroup.transvection hij 1)
    (hconstant 1)
  have hi : Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ) *
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) = 1 := by
    simpa only [neg_neg] using Matrix.SpecialLinearGroup.transvection_mul_neg hij (-1 : ℝ)
  rw [mul_assoc, hi, mul_one] at hm
  exact hm.symm

end DukePrimeDegree

end OAI
