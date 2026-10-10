import OAI.NumberTheory.Ostmann.Construction.HistoryCoprimalityRemoval
import OAI.NumberTheory.Ostmann.Construction.HistoryPolynomialSpecialization

namespace OAI

/-! # Constructed integer numerators for the recursive pivot substitutions -/

namespace Ostmann

open scoped BigOperators Classical

structure ClearedHistoryValue (σ : Type*) where
  numerator : MvPolynomial σ ℤ
  denominator : ℤ
  denominator_ne_zero : denominator ≠ 0

namespace ClearedHistoryValue

variable {σ : Type*}

noncomputable def ofVariable (i : σ) : ClearedHistoryValue σ := ⟨MvPolynomial.X i, 1, one_ne_zero⟩

noncomputable def constant (a : ℤ) : ClearedHistoryValue σ := ⟨MvPolynomial.C a, 1, one_ne_zero⟩

noncomputable def prod {I : Type*} (S : Finset I) (f : I → ClearedHistoryValue σ) :
    ClearedHistoryValue σ :=
  ⟨∏ i ∈ S, (f i).numerator, ∏ i ∈ S, (f i).denominator,
    Finset.prod_ne_zero_iff.mpr (fun i _ => (f i).denominator_ne_zero)⟩

/-- This is exactly `(v * right - w * left) / s`, with integer clearing of
all previously inserted denominators. -/
noncomputable def pivot (left right : ClearedHistoryValue σ) (v w s : ℤ) (hs : s ≠ 0) :
    ClearedHistoryValue σ :=
  ⟨MvPolynomial.C (v * left.denominator) * right.numerator -
      MvPolynomial.C (w * right.denominator) * left.numerator,
    s * left.denominator * right.denominator,
    mul_ne_zero (mul_ne_zero hs left.denominator_ne_zero) right.denominator_ne_zero⟩

noncomputable def eval (F : ClearedHistoryValue σ) (x : σ → ℚ) : ℚ :=
  MvPolynomial.eval₂ (Int.castRingHom ℚ) x F.numerator / F.denominator

theorem eval_variable (i : σ) (x : σ → ℚ) : (ofVariable i).eval x = x i := by
  simp only [eval, ofVariable, MvPolynomial.eval₂_X, Int.cast_one, div_one]

theorem eval_constant (a : ℤ) (x : σ → ℚ) : (constant a).eval x = a := by
  simp only [eval, constant, MvPolynomial.eval₂_C, Int.cast_one, div_one]
  rfl

theorem eval_prod {I : Type*} (S : Finset I) (f : I → ClearedHistoryValue σ) (x : σ → ℚ) :
    (prod S f).eval x = ∏ i ∈ S, (f i).eval x := by
  simp only [eval, prod, MvPolynomial.eval₂_eq_eval_map, map_prod, Finset.prod_div_distrib]
  push_cast
  rfl

theorem eval_pivot (left right : ClearedHistoryValue σ) (v w s : ℤ) (hs : s ≠ 0)
    (x : σ → ℚ) :
    (pivot left right v w s hs).eval x = (v * right.eval x - w * left.eval x) / s := by
  have hL : (left.denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr left.denominator_ne_zero
  have hR : (right.denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr right.denominator_ne_zero
  have hS : (s : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs
  simp only [eval, pivot, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, Int.coe_castRingHom, Int.cast_mul]
  field_simp

theorem degree_prod {I : Type*} (S : Finset I) (f : I → ClearedHistoryValue σ) :
    (prod S f).numerator.totalDegree ≤ ∑ i ∈ S, (f i).numerator.totalDegree :=
  MvPolynomial.totalDegree_finsetProd _ _

theorem degree_pivot (left right : ClearedHistoryValue σ) (v w s : ℤ) (hs : s ≠ 0) :
    (pivot left right v w s hs).numerator.totalDegree ≤
      max left.numerator.totalDegree right.numerator.totalDegree := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact le_max_right _ _)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact le_max_left _ _)

/-- A prime absent from the small-frequency denominator remains absent after
the next substitution. -/
theorem denominator_pivot_unit (left right : ClearedHistoryValue σ)
    (v w s : ℤ) (hs : s ≠ 0) (p : ℕ) (hp : p.Prime)
    (hL : ¬p ∣ left.denominator.natAbs) (hR : ¬p ∣ right.denominator.natAbs)
    (hS : ¬p ∣ s.natAbs) : ¬p ∣ (pivot left right v w s hs).denominator.natAbs := by
  simp only [pivot, Int.natAbs_mul, hp.dvd_mul, hL, hR, hS, or_self, not_false_eq_true]

/-- Polynomial evaluation at an integer assignment is the numerator of the
actual rational value. The equality is useful on the integrality support. -/
theorem integer_value_cleared (F : ClearedHistoryValue σ) (x : σ → ℤ) (y : ℤ)
    (hy : F.eval (fun i => (x i : ℚ)) = y) :
    MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.numerator = F.denominator * y := by
  have hden : (F.denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr F.denominator_ne_zero
  have he : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.numerator : ℚ) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (x i : ℚ)) F.numerator := by
    simpa [Int.castRingHom] using
      (MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F.numerator)
  apply Int.cast_injective (α := ℚ)
  rw [he, Int.cast_mul]
  have hh := (div_eq_iff hden).mp hy
  simpa only [mul_comm] using hh

theorem prime_coprime_integer_value (F : ClearedHistoryValue σ) (x : σ → ℤ)
    (p : ℕ) (hp : p.Prime) (hd : ¬p ∣ F.denominator.natAbs) (y : ℤ)
    (hy : F.eval (fun i => (x i : ℚ)) = y) :
    p.Coprime y.natAbs ↔ ¬p ∣ (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.numerator).natAbs := by
  rw [hp.coprime_iff_not_dvd, prime_dvd_cleared_iff p hp _ F.denominator y
    (F.integer_value_cleared x y hy) hd]

end ClearedHistoryValue

end Ostmann

end OAI
