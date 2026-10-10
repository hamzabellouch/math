import Mathlib

namespace OAI
open scoped BigOperators
namespace Problem337

lemma prime_dvd_num_of_fraction (p a b : ℕ) (hp : p.Prime)
    (hb : b ≠ 0) (hpb : p ∣ b) (q : ℚ)
    (hq : q = (a : ℚ) / b) (hden : ¬p ∣ q.den) : p ∣ a := by
  have hq' : q = Rat.divInt (a : ℤ) (b : ℤ) := by
    simpa only [Rat.divInt_eq_div, Int.cast_natCast] using hq
  obtain ⟨c, ha, hb'⟩ := Rat.num_den_mk (by exact_mod_cast hb) hq'
  have hbabs : b = c.natAbs * q.den := by
    have h := congrArg Int.natAbs hb'
    simpa only [Int.natAbs_natCast, Int.natAbs_mul] using h
  have habs : a = c.natAbs * q.num.natAbs := by
    have h := congrArg Int.natAbs ha
    simpa only [Int.natAbs_natCast, Int.natAbs_mul] using h
  rw [hbabs] at hpb
  have hpc : p ∣ c.natAbs := (hp.dvd_mul.mp hpb).resolve_right hden
  rw [habs]
  exact dvd_mul_of_dvd_left hpc _

lemma prime_not_dvd_den_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (p : ℕ) (hp : p.Prime) (hf : ∀ i ∈ s, ¬p ∣ (f i).den) :
    ¬p ∣ (∑ i ∈ s, f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp.not_dvd_one
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      intro hd
      have hprod := hd.trans (Rat.add_den_dvd (f a) (∑ i ∈ s, f i))
      rcases hp.dvd_mul.mp hprod with h | h
      · exact hf a (by simp) h
      · exact ih (fun i hi => hf i (by simp [hi])) h

lemma prime_not_dvd_den_unit_sum {ι : Type*} (s : Finset ι) (n : ι → ℕ)
    (p : ℕ) (hp : p.Prime) (hn : ∀ i ∈ s, 0 < n i ∧ n i < p) :
    ¬p ∣ (∑ i ∈ s, (1 : ℚ) / n i).den := by
  apply prime_not_dvd_den_sum s _ p hp
  intro i hi
  have hni := hn i hi
  simpa [one_div, Rat.den_inv, ne_of_gt hni.1] using
    (Nat.not_dvd_of_pos_of_lt hni.1 hni.2)


lemma prime_successor_unit_obstruction (p : ℕ) (hp : p.Prime)
    (x : ℚ) (hx : ¬p ∣ x.den) :
    x + 1 / (p : ℚ) + 1 / ((p + 1 : ℕ) : ℚ) ≠ 1 := by
  intro h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : ((p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hid : 1 / (p : ℚ) + 1 / ((p + 1 : ℕ) : ℚ) =
      ((2 * p + 1 : ℕ) : ℚ) / ((p * (p + 1) : ℕ) : ℚ) := by
    push_cast
    field_simp
    ring
  have hq : 1 - x = ((2 * p + 1 : ℕ) : ℚ) / ((p * (p + 1) : ℕ) : ℚ) := by
    rw [← hid]
    linarith
  have hd : ¬p ∣ (1 - x).den := by simpa using hx
  have hh := prime_dvd_num_of_fraction p (2*p+1) (p*(p+1)) hp
    (Nat.mul_ne_zero hp.ne_zero (by omega)) (dvd_mul_right _ _) (1-x) hq hd
  exact hp.not_dvd_one ((Nat.dvd_add_iff_right (dvd_mul_left p 2)).mpr hh)

lemma prime_product_unit_obstruction (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (x : ℚ) (hx : ¬p ∣ x.den) :
    x + 1 / (p : ℚ) + 1 / ((p * (p + 1) : ℕ) : ℚ) ≠ 1 := by
  intro h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : ((p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hid : 1 / (p : ℚ) + 1 / ((p * (p + 1) : ℕ) : ℚ) =
      ((p + 2 : ℕ) : ℚ) / ((p * (p + 1) : ℕ) : ℚ) := by
    push_cast
    field_simp
    ring
  have hq : 1 - x = ((p + 2 : ℕ) : ℚ) / ((p * (p + 1) : ℕ) : ℚ) := by
    rw [← hid]
    linarith
  have hd : ¬p ∣ (1 - x).den := by simpa using hx
  have hh := prime_dvd_num_of_fraction p (p+2) (p*(p+1)) hp
    (Nat.mul_ne_zero hp.ne_zero (by omega)) (dvd_mul_right _ _) (1-x) hq hd
  have hh2 : p ∣ 2 := (Nat.dvd_add_iff_right (dvd_refl p)).mpr hh
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hh2

lemma prime_successor_prefix_obstruction {ι : Type*} (s : Finset ι) (n : ι → ℕ)
    (p : ℕ) (hp : p.Prime) (hn : ∀ i ∈ s, 0 < n i ∧ n i < p) :
    (∑ i ∈ s, (1 : ℚ) / n i) + 1 / (p : ℚ) +
      1 / ((p + 1 : ℕ) : ℚ) ≠ 1 :=
  prime_successor_unit_obstruction p hp _ (prime_not_dvd_den_unit_sum s n p hp hn)

lemma prime_product_prefix_obstruction {ι : Type*} (s : Finset ι) (n : ι → ℕ)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hn : ∀ i ∈ s, 0 < n i ∧ n i < p) :
    (∑ i ∈ s, (1 : ℚ) / n i) + 1 / (p : ℚ) +
      1 / ((p * (p + 1) : ℕ) : ℚ) ≠ 1 :=
  prime_product_unit_obstruction p hp hp3 _ (prime_not_dvd_den_unit_sum s n p hp hn)

end Problem337

end OAI
