import OAI.NumberTheory.EgyptianFractions.MarkedGroupingUnits

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A supply of at most `B` rational divisors can only represent integers
up to `B*K`, since each positive rational divisor is at most `K`. -/
theorem rational_supply_forces_size (m K B : ℕ) (hm : 1 ≤ m) (hK : 0 < K)
    (hsupply : HasRationalDivisorSupply m K B) : m ^ 4 ≤ B * K := by
  obtain ⟨terms, hlen, hterms, hsum⟩ := hsupply (m ^ 4) (one_le_pow₀ hm) le_rfl
  have hterm : ∀ et ∈ terms, (et.1 : ℚ) / (et.2 : ℚ) ≤ (K : ℚ) := by
    intro et het
    obtain ⟨he, heK, ht⟩ := hterms et het
    have he_le : et.1 ≤ K := Nat.le_of_dvd hK heK
    have htR : (1 : ℚ) ≤ et.2 := by exact_mod_cast ht
    have heR : (0 : ℚ) ≤ et.1 := by positivity
    calc
      (et.1 : ℚ) / (et.2 : ℚ) ≤ (et.1 : ℚ) := div_le_self heR htR
      _ ≤ (K : ℚ) := by exact_mod_cast he_le
  have hsum_le : (terms.map (fun et => (et.1 : ℚ) / (et.2 : ℚ))).sum ≤
      (terms.length : ℚ) * K := by
    clear hsum hlen hterms
    induction terms with
    | nil => simp
    | cons et terms ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      have hhead := hterm et (by simp)
      have htail := ih (by intro a ha; exact hterm a (by simp [ha]))
      nlinarith
  have hlenR : (terms.length : ℚ) ≤ B := by exact_mod_cast hlen
  have hfinal : ((m ^ 4 : ℕ) : ℚ) ≤ (B : ℚ) * K := by
    rw [← hsum]
    exact hsum_le.trans (mul_le_mul_of_nonneg_right hlenR (by positivity))
  exact_mod_cast hfinal

/-- With sixteen summands, the full supply already forces the auxiliary
integer to exceed the marker by a large margin. -/
theorem rational_supply_forces_large_auxiliary (m K : ℕ) (hm : 4 ≤ m)
    (hK : 0 < K) (hsupply : HasRationalDivisorSupply m K 16) : m ^ 2 ≤ K := by
  have hbound := rational_supply_forces_size m K 16 (by omega) hK hsupply
  have hm2 : 16 ≤ m ^ 2 := by nlinarith
  have hprod := Nat.mul_le_mul_right (m ^ 2) hm2
  have hpow : m ^ 2 * m ^ 2 = m ^ 4 := by ring
  rw [hpow] at hprod
  have hfinal := hprod.trans hbound
  omega

end Problem337

end

end OAI
