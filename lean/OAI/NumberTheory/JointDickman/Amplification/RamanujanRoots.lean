import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace OAI

/-! # Primitive-root sums and the Ramanujan factor -/

namespace JointDickman

open Finset Polynomial
open scoped ArithmeticFunction.Moebius

theorem stdAddChar_natCast {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = Complex.exp (2 * Real.pi * Complex.I * n / q) := by
  simpa only [Int.cast_natCast] using
    ZMod.stdAddChar_coe (N := q) (n : ℤ)

theorem stdAddChar_eq_primitive_power {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = Complex.exp (2 * Real.pi * Complex.I / q) ^ n := by
  rw [stdAddChar_natCast, ← Complex.exp_nat_mul]
  congr 1
  ring

open Classical in
theorem nthRoots_image_stdAddChar (q : ℕ) [NeZero q] :
    nthRootsFinset q (1 : ℂ) = univ.image (ZMod.stdAddChar (N := q)) := by
  ext z
  rw [mem_nthRootsFinset (NeZero.pos q), mem_image]
  constructor
  · intro hz
    obtain ⟨i, _, hi⟩ := (Complex.isPrimitiveRoot_exp q (NeZero.ne q)).eq_pow_of_pow_eq_one hz
    exact ⟨(i : ZMod q), mem_univ _, (stdAddChar_eq_primitive_power i).trans hi⟩
  · rintro ⟨r, _, rfl⟩
    rw [← ZMod.natCast_zmod_val r, stdAddChar_eq_primitive_power, ← pow_mul,
      mul_comm r.val q, pow_mul, (Complex.isPrimitiveRoot_exp q (NeZero.ne q)).pow_eq_one,
      one_pow]

open Classical in
theorem sum_nthRoots_one (q : ℕ) (hq : 0 < q) :
    ∑ z ∈ nthRootsFinset q (1 : ℂ), z = if q = 1 then 1 else 0 := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [nthRoots_image_stdAddChar, sum_image]
  · by_cases hq1 : q = 1
    · subst q
      simp only [Fintype.sum_unique, ite_true]
      convert! (ZMod.stdAddChar (N := 1)).map_zero_eq_one using 1
    · rw [ite_eq_right hq1]
      apply AddChar.sum_eq_zero_of_ne_one
      intro h
      have hh : ZMod.stdAddChar (1 : ZMod q) = ZMod.stdAddChar (0 : ZMod q) := by rw [h]; rfl
      have h10 := ZMod.injective_stdAddChar hh
      have hq2 : 1 < q := by omega
      let : Fact (1 < q) := ⟨hq2⟩
      exact one_ne_zero h10
  · exact fun _ _ _ _ h => ZMod.injective_stdAddChar h

open Classical in
theorem sum_primitiveRoots_eq_moebius (q : ℕ) (hq : 0 < q) :
    ∑ z ∈ primitiveRoots q ℂ, z = (μ q : ℂ) := by
  have hdiv : ∀ n > 0,
      ∑ d ∈ n.divisors, (∑ z ∈ primitiveRoots d ℂ, z) =
        (if n = 1 then (1 : ℂ) else 0) := by
    intro n hn
    rw [← sum_nthRoots_one n hn, IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
      sum_biUnion]
    intro i _ j _ hij
    exact IsPrimitiveRoot.disjoint hij
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hdiv) q hq
  rw [sum_eq_single (q, 1)] at h
  · simpa using h.symm
  · rintro ⟨a, b⟩ hab hne
    by_cases hb : b = 1
    · have habq := (Nat.mem_divisorsAntidiagonal.mp hab).1
      have ha : a = q := by simpa only [hb, mul_one] using habq
      exact False.elim (hne (Prod.ext ha hb))
    · simp [hb]
  · simp [Nat.mem_divisorsAntidiagonal, hq.ne']

end JointDickman

end OAI
