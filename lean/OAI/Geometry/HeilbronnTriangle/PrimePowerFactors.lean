import Mathlib

namespace OAI


namespace Problem355.PrimePowerFactors

theorem exists_pow_mul_unit {p : ℕ} (hp : p.Prime) (k : ℕ)
    (x : ZMod (p ^ k)) :
    ∃ e ≤ k, ∃ u : (ZMod (p ^ k))ˣ,
      x = (p : ZMod (p ^ k)) ^ e * (u : ZMod (p ^ k)) := by
  obtain ⟨d, hd, v, hv, hx⟩ := ZMod.eq_unit_mul_divisor x
  obtain ⟨e, he, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
  obtain ⟨u, rfl⟩ := hv
  exact ⟨e, he, u, by simpa [Nat.cast_pow, mul_comm] using hx⟩

theorem exists_least_power_factor {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℕ} (hp : p.Prime) (k : ℕ) (x : ι → ZMod (p ^ k)) :
    ∃ i : ι, ∃ e ≤ k, ∃ u : (ZMod (p ^ k))ˣ,
      x i = (p : ZMod (p ^ k)) ^ e * (u : ZMod (p ^ k)) ∧
      ∀ j, (p : ZMod (p ^ k)) ^ e ∣ x j := by
  classical
  choose e he u hu using fun i => exists_pow_mul_unit hp k (x i)
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  refine ⟨i, e i, he i, u i, hu i, ?_⟩
  intro j
  rw [hu j]
  exact dvd_mul_of_dvd_left (pow_dvd_pow _ (hmin j (Finset.mem_univ j))) _

theorem exists_dvd_all {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℕ} (hp : p.Prime) (k : ℕ) (x : ι → ZMod (p ^ k)) :
    ∃ i : ι, ∀ j, x i ∣ x j := by
  obtain ⟨i, e, he, u, hu, hdiv⟩ := exists_least_power_factor hp k x
  refine ⟨i, fun j => ?_⟩
  rw [hu]
  obtain ⟨z, hz⟩ := hdiv j
  refine ⟨(↑(u⁻¹) : ZMod (p ^ k)) * z, ?_⟩
  simpa [mul_assoc] using hz

theorem pow_dvd_pow_iff {p : ℕ} (hp : p.Prime) {k b e : ℕ}
    (hb : b ≤ k) :
    ((p : ZMod (p ^ k)) ^ b ∣ (p : ZMod (p ^ k)) ^ e) ↔ b ≤ e := by
  constructor
  · intro hd
    by_contra hbe
    have heb : e + 1 ≤ b := by omega
    have hek : e + 1 ≤ k := heb.trans hb
    let f : ZMod (p ^ k) →+* ZMod (p ^ (e + 1)) :=
      ZMod.castHom (pow_dvd_pow p hek) (ZMod (p ^ (e + 1)))
    have hzero : (p : ZMod (p ^ (e + 1))) ^ b = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact pow_dvd_pow p heb
    obtain ⟨z, hz⟩ := hd
    have hcast := congrArg f hz
    have hsmallzero : (p : ZMod (p ^ (e + 1))) ^ e = 0 := by
      simpa only [map_pow, map_natCast, map_mul, hzero, zero_mul] using hcast
    have hnat : p ^ (e + 1) ∣ p ^ e := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      simpa only [Nat.cast_pow] using hsmallzero
    have hbad := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hnat
    omega
  · exact fun hbe => pow_dvd_pow _ hbe

theorem pow_dvd_pow_mul_unit_iff {p : ℕ} (hp : p.Prime) {k b e : ℕ}
    (hb : b ≤ k) (u : (ZMod (p ^ k))ˣ) :
    ((p : ZMod (p ^ k)) ^ b ∣ (p : ZMod (p ^ k)) ^ e * ↑u) ↔ b ≤ e := by
  rw [← pow_dvd_pow_iff hp hb]
  constructor
  · intro hd
    simpa [mul_assoc] using dvd_mul_of_dvd_left hd (↑(u⁻¹) : ZMod (p ^ k))
  · exact fun hd => dvd_mul_of_dvd_left hd _

theorem exists_ordered_factors {p : ℕ} (hp : p.Prime) (k : ℕ)
    (x y : ZMod (p ^ k)) (hxy : x ∣ y) :
    ∃ b e : ℕ, b ≤ e ∧ e ≤ k ∧
      ∃ u v : (ZMod (p ^ k))ˣ,
        x = (p : ZMod (p ^ k)) ^ b * ↑u ∧
        y = (p : ZMod (p ^ k)) ^ e * ↑v := by
  obtain ⟨b, hb, u, hx⟩ := exists_pow_mul_unit hp k x
  obtain ⟨e, he, v, hy⟩ := exists_pow_mul_unit hp k y
  refine ⟨b, e, ?_, he, u, v, hx, hy⟩
  apply (pow_dvd_pow_mul_unit_iff hp hb v).mp
  rw [← hy]
  apply dvd_trans ?_ hxy
  rw [hx]
  exact dvd_mul_right _ _

end Problem355.PrimePowerFactors

end OAI
