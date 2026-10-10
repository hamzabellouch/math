import Mathlib

namespace OAI
namespace Problem337.DivisorMoment

/-- Positive divisors truncated at an integral threshold. -/
def truncatedDivisors (X n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun a => a ≤ X)

@[simp] theorem mem_truncatedDivisors {X n a : ℕ} :
    a ∈ truncatedDivisors X n ↔ a ∣ n ∧ n ≠ 0 ∧ a ≤ X := by
  simp [truncatedDivisors, and_assoc]

/-- The second component of the gcd splitting is a divisor of the quotient.
No coprimality of the chosen factor and the quotient is needed. -/
theorem div_gcd_dvd_quotient {a d n : ℕ} (ha : a ∣ n) (hd : d ∣ n) :
    a / Nat.gcd a d ∣ n / d := by
  apply (Nat.dvd_div_iff_mul_dvd hd).2
  have hlcm : Nat.lcm a d = d * (a / Nat.gcd a d) := by
    rw [Nat.lcm_eq_mul_div, Nat.mul_comm a d,
      Nat.mul_div_assoc d (Nat.gcd_dvd_left a d)]
  rw [← hlcm]
  exact Nat.lcm_dvd ha hd

/-- Divisor splitting is injective, because its components multiply to the input. -/
theorem gcd_split_injective (d : ℕ) :
    Function.Injective (fun a : ℕ => (Nat.gcd a d, a / Nat.gcd a d)) := by
  intro a b hab
  have h := congrArg (fun z : ℕ × ℕ => z.2 * z.1) hab
  simpa only [Nat.div_mul_cancel (Nat.gcd_dvd_left a d),
    Nat.div_mul_cancel (Nat.gcd_dvd_left b d)] using h

/-- Truncated divisors of a product inject into a full divisor set and one
truncated divisor set. This is the prefix inequality in the divisor moment argument. -/
theorem truncated_card_le_mul {X n d : ℕ} (hn : 0 < n) (hd : d ∣ n) :
    (truncatedDivisors X n).card ≤
      d.divisors.card * (truncatedDivisors X (n / d)).card := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  have hquotpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hd) hdpos
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun a : ℕ => (Nat.gcd a d, a / Nat.gcd a d))
  · intro a ha
    obtain ⟨han, _, haX⟩ := mem_truncatedDivisors.mp ha
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right a d, hdpos.ne'⟩
    · exact mem_truncatedDivisors.mpr
        ⟨div_gcd_dvd_quotient han hd, hquotpos.ne',
          (Nat.div_le_self a (Nat.gcd a d)).trans haX⟩
  · exact (gcd_split_injective d).injOn

/-- Multiples of a positive integer in a translated interval satisfy the
uniform counting estimate needed for short-interval divisor moments. -/
theorem interval_multiples_card_le (N Y d : ℕ) (hd : 0 < d) :
    ((Finset.Ioc N (N + Y)).filter (fun a => d ∣ a)).card ≤ Y / d + 1 := by
  have hcard : ((Finset.Ioc N (N + Y)).filter (fun a => d ∣ a)).card ≤
      (Finset.Ioc (N / d) ((N + Y) / d)).card := by
    apply Finset.card_le_card_of_injOn (fun a : ℕ => a / d)
    · intro a ha
      obtain ⟨haI, had⟩ := Finset.mem_filter.mp ha
      obtain ⟨hNa, haNY⟩ := Finset.mem_Ioc.mp haI
      apply Finset.mem_Ioc.mpr
      constructor
      · apply (Nat.div_lt_iff_lt_mul hd).mpr
        simpa only [Nat.div_mul_cancel had] using hNa
      · exact Nat.div_le_div_right haNY
    · intro a ha b hb hab
      have had := (Finset.mem_filter.mp ha).2
      have hbd := (Finset.mem_filter.mp hb).2
      have h := congrArg (fun q => q * d) hab
      simpa only [Nat.div_mul_cancel had, Nat.div_mul_cancel hbd] using h
  rw [Nat.card_Ioc, Nat.add_div hd] at hcard
  split_ifs at hcard
  · simpa only [Nat.add_assoc, Nat.add_sub_cancel_left] using hcard
  · have h : ((Finset.Ioc N (N + Y)).filter (fun a => d ∣ a)).card ≤ Y / d := by
      simpa only [Nat.add_zero, Nat.add_sub_cancel_left] using hcard
    exact h.trans (Nat.le_succ _)

theorem interval_multiples_card_le_real (N Y d : ℕ) (hd : 0 < d) :
    (((Finset.Ioc N (N + Y)).filter (fun a => d ∣ a)).card : ℝ) ≤
      (Y : ℝ) / d + 1 := by
  calc
    _ ≤ ((Y / d + 1 : ℕ) : ℝ) := by
      exact_mod_cast interval_multiples_card_le N Y d hd
    _ = ((Y / d : ℕ) : ℝ) + 1 := by norm_cast
    _ ≤ (Y : ℝ) / d + 1 := by
      have hcast : ((Y / d : ℕ) : ℝ) ≤ (Y : ℝ) / d := Nat.cast_div_le
      linarith

theorem interval_multiples_card_le_twice (N Y d : ℕ) (hd : 0 < d)
    (hdY : d ≤ Y) :
    (((Finset.Ioc N (N + Y)).filter (fun a => d ∣ a)).card : ℝ) ≤
      2 * (Y : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio : (1 : ℝ) ≤ (Y : ℝ) / d := by
    apply (le_div_iff₀ hdR).mpr
    simpa only [one_mul] using (show (d : ℝ) ≤ Y by exact_mod_cast hdY)
  calc
    _ ≤ (Y : ℝ) / d + 1 := interval_multiples_card_le_real N Y d hd
    _ ≤ 2 * ((Y : ℝ) / d) := by linarith
    _ = 2 * (Y : ℝ) / d := by ring

/-- Real lengths are implemented by their natural floor, without changing the
uniform interval bound. -/
theorem interval_multiples_real_cutoff (N d : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (hd : 0 < d) :
    (((Finset.Ioc N (N + ⌊Y⌋₊)).filter (fun a => d ∣ a)).card : ℝ) ≤
      Y / d + 1 := by
  calc
    _ ≤ (⌊Y⌋₊ : ℝ) / d + 1 := interval_multiples_card_le_real N ⌊Y⌋₊ d hd
    _ ≤ Y / d + 1 := by
      gcongr
      exact Nat.floor_le hY

theorem interval_multiples_real_cutoff_twice (N d : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (hd : 0 < d) (hdY : (d : ℝ) ≤ Y) :
    (((Finset.Ioc N (N + ⌊Y⌋₊)).filter (fun a => d ∣ a)).card : ℝ) ≤
      2 * Y / d := by
  calc
    _ ≤ 2 * (⌊Y⌋₊ : ℝ) / d :=
      interval_multiples_card_le_twice N ⌊Y⌋₊ d hd (Nat.le_floor hdY)
    _ ≤ 2 * Y / d := by
      gcongr
      exact Nat.floor_le hY

end Problem337.DivisorMoment

end OAI
