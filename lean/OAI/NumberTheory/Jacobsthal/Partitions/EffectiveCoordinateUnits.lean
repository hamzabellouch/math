import OAI.NumberTheory.Jacobsthal.Paths.ActualEffectiveWitness

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective

theorem actual_m0_coprime (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) :
    (intervalM0 p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf)).natAbs.Coprime
      (effectiveModulus a r qf) := by
  apply Nat.coprime_of_dvd
  intro t ht htm htH
  have htm' : (t : ℤ) ∣ intervalM0 p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) :=
    Int.natCast_dvd.mpr htm
  have htH' : (t : ℤ) ∣ (effectiveModulus a r qf : ℤ) := by exact_mod_cast htH
  have hdiff := (intervalM0_modEq p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf)).dvd
  have hC : (t : ℤ) ∣ effectiveIntercept a r qf := by
    have ha := dvd_add (htH'.trans hdiff) (dvd_mul_of_dvd_right htm' (p : ℤ))
    simpa only [sub_add_cancel] using ha
  have hdiv := Nat.dvd_gcd (Int.natCast_dvd.mp hC) htH
  rw [(effectiveIntercept_coprime a r qf hq).gcd_eq_one] at hdiv
  exact ht.not_dvd_one hdiv

end ErdosVarianceEffective

end

end Erdos970

end OAI
