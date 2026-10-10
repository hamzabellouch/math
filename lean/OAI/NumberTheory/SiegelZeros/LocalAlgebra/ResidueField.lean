import Mathlib.Algebra.CharP.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int

namespace OAI

namespace SiegelZeros


open scoped NumberField

namespace SiegelZerosAwei.W38

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

theorem exists_maximal_above_prime :
    ∃ Q : Ideal (𝓞 K), Q.IsMaximal ∧ Q.LiesOver (Ideal.span {(p : ℤ)}) :=
  Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)})

noncomputable def primeIdealAbove : Ideal (𝓞 K) :=
  (exists_maximal_above_prime K p).choose

instance primeIdealAbove_isMaximal : (primeIdealAbove K p).IsMaximal :=
  (exists_maximal_above_prime K p).choose_spec.1

instance primeIdealAbove_liesOver :
    (primeIdealAbove K p).LiesOver (Ideal.span {(p : ℤ)}) :=
  (exists_maximal_above_prime K p).choose_spec.2

abbrev PrimeResidueField : Type _ := (𝓞 K) ⧸ primeIdealAbove K p

noncomputable instance primeResidueField_field : Field (PrimeResidueField K p) :=
  Ideal.Quotient.field (primeIdealAbove K p)

instance primeResidueField_charP : CharP (PrimeResidueField K p) p := by
  apply (CharP.charP_iff_prime_eq_zero (R := PrimeResidueField K p)
    (Fact.out : p.Prime)).mpr
  change Ideal.Quotient.mk (primeIdealAbove K p) (p : 𝓞 K) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  simpa only [map_natCast] using
    (Ideal.mem_of_liesOver (primeIdealAbove K p) (Ideal.span {(p : ℤ)}) (p : ℤ)).mp
      (Ideal.mem_span_singleton_self _)

noncomputable def primeReduction : 𝓞 K →+* PrimeResidueField K p :=
  Ideal.Quotient.mk (primeIdealAbove K p)

theorem residue_natCast_ne_zero {n : ℕ} (hn : ¬ p ∣ n) :
    (n : PrimeResidueField K p) ≠ 0 := by
  exact fun h => hn ((CharP.cast_eq_zero_iff (PrimeResidueField K p) p n).mp h)

theorem primeReduction_natCast_ne_zero {n : ℕ} (hn : ¬ p ∣ n) :
    primeReduction K p (n : 𝓞 K) ≠ 0 := by
  simpa only [map_natCast] using residue_natCast_ne_zero K p hn

end SiegelZerosAwei.W38


end SiegelZeros

end OAI
