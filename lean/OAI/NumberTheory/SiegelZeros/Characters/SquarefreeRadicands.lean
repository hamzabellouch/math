import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Rat.Lemmas
import OAI.NumberTheory.SiegelZeros.Structure.FieldAutomorphisms

namespace OAI

namespace SiegelZeros


namespace W10

theorem squarefree_int_eq_one_of_rational_square (d : ℤ) (hd : Squarefree d)
    (x : ℚ) (hx : x ^ 2 = (d : ℚ)) : d = 1 := by
  have his : IsSquare (d : ℚ) := ⟨x, by simpa [pow_two] using hx.symm⟩
  obtain ⟨z, hz⟩ := Rat.isSquare_intCast_iff.mp his
  have hzu : IsUnit z := hd z (by rw [hz])
  rcases Int.isUnit_iff.mp hzu with h | h
  · simpa [h] using hz
  · simpa [h] using hz

theorem squarefree_int_eq_two_of_twice_rational_square (d : ℤ) (hd : Squarefree d)
    (x : ℚ) (hx : x ^ 2 = 2 * (d : ℚ)) : d = 2 := by
  have his : IsSquare ((2 * d : ℤ) : ℚ) :=
    ⟨x, by simpa [pow_two] using hx.symm⟩
  obtain ⟨z, hz⟩ := Rat.isSquare_intCast_iff.mp his
  have hzdiv : d ∣ z ^ 2 := by
    rw [pow_two, ← hz]
    exact dvd_mul_left d 2
  obtain ⟨k, hk⟩ := (hd.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hzdiv
  have hk2 : d * (k * k) = 2 := by
    apply mul_left_cancel₀ hd.ne_zero
    calc
      d * (d * (k * k)) = (d * k) * (d * k) := by ring
      _ = 2 * d := by rw [← hk, ← hz]
      _ = d * 2 := mul_comm 2 d
  have hku : IsUnit k := Int.prime_two.squarefree k
    ⟨d, by simpa [mul_comm] using hk2.symm⟩
  rcases Int.isUnit_iff.mp hku with h | h
  · simpa [h] using hk2
  · simpa [h] using hk2

theorem rational_sq_ne_squarefree_int (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1)
    (x : ℚ) : x ^ 2 ≠ (d : ℚ) := by
  intro h
  exact hd1 (squarefree_int_eq_one_of_rational_square d hd x h)

theorem rational_sq_ne_twice_squarefree_int (d : ℤ) (hd : Squarefree d) (hd2 : d ≠ 2)
    (x : ℚ) : x ^ 2 ≠ 2 * (d : ℚ) := by
  intro h
  exact hd2 (squarefree_int_eq_two_of_twice_rational_square d hd x h)

theorem generators_linearIndependent_squarefree
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (a b : K) (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    LinearIndependent ℚ (generators a b) := by
  apply generators_linearIndependent_sqrt_two a b (d : ℚ) (by simpa using ha) hb
    (rational_sq_ne_squarefree_int d hd hd1)
    (rational_sq_ne_twice_squarefree_int d hd hd2)

end W10


end SiegelZeros

end OAI
