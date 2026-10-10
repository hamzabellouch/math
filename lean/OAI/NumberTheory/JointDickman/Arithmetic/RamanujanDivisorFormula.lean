import OAI.NumberTheory.JointDickman.Probability.ResidueFourierParseval

namespace OAI

/-! # An exact divisor formula for all Ramanujan frequencies -/

namespace JointDickman
open Finset
open scoped ArithmeticFunction.Moebius

noncomputable def ramanujanSum (q : ℕ) [NeZero q] (h : ZMod q) : ℂ :=
  ∑ r : (ZMod q)ˣ, ZMod.stdAddChar (h*(r : ZMod q))

theorem ramanujanSum_zero (q : ℕ) [NeZero q] :
    ramanujanSum q 0 = q.totient := by
  simp [ramanujanSum,ZMod.card_units_eq_totient]

theorem ramanujanSum_unit {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    ramanujanSum q u = (μ q : ℂ) := ramanujan_sum_unit_frequency u

theorem sum_nthRoots_power (q : ℕ) (hq : 0 < q) (k : ℕ) :
    (∑ z ∈ Polynomial.nthRootsFinset q (1 : ℂ), z^k) =
      if q ∣ k then (q : ℂ) else 0 := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [nthRoots_image_stdAddChar,sum_image]
  · simp_rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    simp_rw [mul_comm (k : ZMod q)]
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
    simp only [ZMod.card,ZMod.natCast_eq_zero_iff]
    split_ifs <;> simp
  · exact fun _ _ _ _ h => ZMod.injective_stdAddChar h

/-- Möbius inversion of the full root sums. This includes nonunit frequencies. -/
theorem sum_primitiveRoots_power (q : ℕ) (hq : 0 < q) (k : ℕ) :
    (∑ z ∈ primitiveRoots q ℂ, z^k) =
      ∑ d ∈ q.divisorsAntidiagonal, (μ d.1 : ℂ)*
        (if d.2 ∣ k then (d.2 : ℂ) else 0) := by
  have hdiv : ∀ n > 0, (∑ d ∈ n.divisors, ∑ z ∈ primitiveRoots d ℂ, z^k) =
      if n ∣ k then (n : ℂ) else 0 := by
    intro n hn
    rw [← sum_nthRoots_power n hn k,IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,sum_biUnion]
    intro i _ j _ hij
    exact IsPrimitiveRoot.disjoint hij
  exact ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hdiv) q hq).symm

theorem ramanujanSum_divisor_formula (q : ℕ) [NeZero q] (k : ℕ) :
    ramanujanSum q (k : ZMod q) =
      ∑ d ∈ q.divisorsAntidiagonal, (μ d.1 : ℂ)*
        (if d.2 ∣ k then (d.2 : ℂ) else 0) := by
  rw [← sum_primitiveRoots_power q (NeZero.pos q) k,primitiveRoots_image_units,sum_image]
  · unfold ramanujanSum
    apply sum_congr rfl
    intro r _
    rw [← AddChar.map_nsmul_eq_pow,nsmul_eq_mul]
  · exact fun _ _ _ _ h => Units.val_injective (ZMod.injective_stdAddChar h)

end JointDickman

end OAI
