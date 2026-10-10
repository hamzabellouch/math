import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeIncidence

namespace OAI

namespace Ostmann.QuadraticCenter

theorem reduced_fraction_preserves_matching {a : ℕ} (ha : 0 < a) (n : ℤ) :
    ∃ h : ℤ, ∃ m : ℕ,
      0 < m ∧ m ≤ a ∧ IsCoprime h (m : ℤ) ∧ h.natAbs ≤ n.natAbs ∧
      ∀ p : ℕ, Nat.Prime p → ¬ p ∣ a → ∀ t : ℤ,
        (p : ℤ) ∣ n - (a : ℤ) * t → (p : ℤ) ∣ h - (m : ℤ) * t := by
  let q : ℚ := Rat.divInt n (a : ℤ)
  have han : (a : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  obtain ⟨c, hnum, hden⟩ := Rat.num_den_mk (q := q) han rfl
  have hcp : 0 < c := by
    have hmp : (0 : ℤ) < q.den := by exact_mod_cast q.pos
    have hap : (0 : ℤ) < a := by exact_mod_cast ha
    rw [hden] at hap
    exact (mul_pos_iff_of_pos_right hmp).mp hap
  have hcabs : 1 ≤ c.natAbs := Int.natAbs_pos.mpr (ne_of_gt hcp)
  have hmdiv : q.den ∣ a := Int.natCast_dvd_natCast.mp (Rat.den_dvd n a)
  refine ⟨q.num, q.den, q.pos, Nat.le_of_dvd ha hmdiv, q.isCoprime_num_den, ?_, ?_⟩
  · rw [hnum, Int.natAbs_mul]
    exact Nat.le_mul_of_pos_left _ hcabs
  · intro p hp hpa t ht
    have hpc : IsCoprime (p : ℤ) c := by
      have hpa' : IsCoprime (p : ℤ) (a : ℤ) :=
        ((hp.coprime_iff_not_dvd).mpr hpa).isCoprime
      exact hpa'.of_isCoprime_of_dvd_right ⟨(q.den : ℤ), hden⟩
    have hfactor : n - (a : ℤ) * t = c * (q.num - (q.den : ℤ) * t) := by
      rw [hnum, hden]
      ring
    rw [hfactor] at ht
    exact hpc.dvd_of_dvd_mul_left ht

end Ostmann.QuadraticCenter

end OAI
