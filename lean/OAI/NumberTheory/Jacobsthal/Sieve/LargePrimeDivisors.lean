import Mathlib

namespace OAI

namespace Erdos970

section

namespace ErdosLineCollision

noncomputable def dividingPrimes (P : Finset ℕ) (m : ℤ) : Finset ℕ := by
  classical
  exact P.filter (fun p => (p : ℤ) ∣ m)

theorem dividingPrimes_card_bound (P : Finset ℕ) (m : ℤ) (hm : m ≠ 0)
    (hprime : ∀ p ∈ P, Nat.Prime p) (z alpha C : ℝ) (hz : 1 < z) (ha : 0 < alpha)
    (hlarge : ∀ p ∈ P, z^alpha ≤ (p : ℝ)) (hheight : |(m : ℝ)| ≤ z^C) :
    ((dividingPrimes P m).card : ℝ) ≤ C/alpha := by
  classical
  have hd : (∏ p ∈ dividingPrimes P m,p) ∣ m.natAbs :=
    Finset.prod_primes_dvd m.natAbs
      (fun p hp => (hprime p (Finset.mem_filter.mp hp).1).prime)
      (fun _ hp => Int.natCast_dvd.mp (Finset.mem_filter.mp hp).2)
  have hprod := Nat.le_of_dvd (Int.natAbs_pos.mpr hm) hd
  have hpow : z^(alpha*((dividingPrimes P m).card : ℝ)) ≤ z^C := by
    calc
      _ = ∏ _p ∈ dividingPrimes P m,z^alpha := by
        rw [Finset.prod_const,Real.rpow_mul_natCast (by linarith : 0 ≤ z)]
      _ ≤ ∏ p ∈ dividingPrimes P m,(p : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg (by linarith) _)
          (fun p hp => hlarge p (Finset.mem_filter.mp hp).1)
      _ = ((∏ p ∈ dividingPrimes P m,p : ℕ) : ℝ) := by simp
      _ ≤ (m.natAbs : ℝ) := by exact_mod_cast hprod
      _ = |(m : ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
      _ ≤ _ := hheight
  have hh := (Real.rpow_le_rpow_left_iff hz).mp hpow
  apply (le_div_iff₀ ha).mpr
  nlinarith

theorem integer_difference_abs_le {x y : ℤ} {S : ℝ}
    (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S) :
    |((x-y : ℤ) : ℝ)| ≤ S := by
  rw [Int.cast_sub,abs_le]
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

end ErdosLineCollision

end

end Erdos970

end OAI
