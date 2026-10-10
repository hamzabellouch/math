import OAI.NumberTheory.EgyptianFractions.TruncatedDivisors

namespace OAI
open scoped BigOperators
namespace Problem337.DivisorMoment

/-- Weighted counting for divisors assigned to integers in a translated
interval. The pfx map need not be injective or canonical. -/
theorem sum_le_assigned_divisor_majorant
    (N Y : ℕ) (A D : Finset ℕ) (pfx : ℕ → ℕ) (w a : ℕ → ℝ)
    (hA : A ⊆ Finset.Ioc N (N + Y))
    (hmap : ∀ n ∈ A, pfx n ∈ D)
    (hdvd : ∀ n ∈ A, pfx n ∣ n)
    (hweight : ∀ n ∈ A, w n ≤ a (pfx n))
    (ha : ∀ d ∈ D, 0 ≤ a d)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ Y) :
    (∑ n ∈ A, w n) ≤ 2 * (Y : ℝ) * ∑ d ∈ D, a d / d := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hmap w, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hfiber : (A.filter (fun n => pfx n = d)) ⊆
      ((Finset.Ioc N (N + Y)).filter (fun n => d ∣ n)) := by
    intro n hn
    obtain ⟨hnA, hnd⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨hA hnA, ?_⟩
    simpa only [hnd] using hdvd n hnA
  have hcard : ((A.filter (fun n => pfx n = d)).card : ℝ) ≤
      2 * (Y : ℝ) / d := by
    calc
      _ ≤ (((Finset.Ioc N (N + Y)).filter (fun n => d ∣ n)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hfiber
      _ ≤ _ := interval_multiples_card_le_twice N Y d (hD d hd).1 (hD d hd).2
  calc
    (∑ n ∈ A with pfx n = d, w n) ≤
        ∑ _n ∈ A with pfx _n = d, a d := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnA, hnd⟩ := Finset.mem_filter.mp hn
      simpa only [hnd] using hweight n hnA
    _ = ((A.filter (fun n => pfx n = d)).card : ℝ) * a d := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (Y : ℝ) / d) * a d :=
      mul_le_mul_of_nonneg_right hcard (ha d hd)
    _ = 2 * (Y : ℝ) * (a d / d) := by ring

/-- A choice-free formulation: every integer only needs some admissible
pfx divisor, with a uniform nonnegative majorant indexed by that divisor. -/
theorem sum_le_divisor_majorant
    (N Y : ℕ) (A D : Finset ℕ) (w a : ℕ → ℝ)
    (hA : A ⊆ Finset.Ioc N (N + Y))
    (hassign : ∀ n ∈ A, ∃ d ∈ D, d ∣ n ∧ w n ≤ a d)
    (ha : ∀ d ∈ D, 0 ≤ a d)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ Y) :
    (∑ n ∈ A, w n) ≤ 2 * (Y : ℝ) * ∑ d ∈ D, a d / d := by
  classical
  choose pfx hpD hpdvd hpw using fun n : A => hassign n n.property
  let p : ℕ → ℕ := fun n => if hn : n ∈ A then pfx ⟨n, hn⟩ else 0
  apply sum_le_assigned_divisor_majorant N Y A D p w a hA
  · intro n hn
    simpa only [p, dite_eq_left hn] using hpD ⟨n, hn⟩
  · intro n hn
    simpa only [p, dite_eq_left hn] using hpdvd ⟨n, hn⟩
  · intro n hn
    simpa only [p, dite_eq_left hn] using hpw ⟨n, hn⟩
  · exact ha
  · exact hD

/-- The short interval may have a real length, as in the uniform divisor
moment statement. No rounding loss is introduced. -/
theorem sum_le_divisor_majorant_real_cutoff
    (N : ℕ) (Y : ℝ) (A D : Finset ℕ) (w a : ℕ → ℝ) (hY : 0 ≤ Y)
    (hA : A ⊆ Finset.Ioc N (N + ⌊Y⌋₊))
    (hassign : ∀ n ∈ A, ∃ d ∈ D, d ∣ n ∧ w n ≤ a d)
    (ha : ∀ d ∈ D, 0 ≤ a d)
    (hD : ∀ d ∈ D, 0 < d ∧ (d : ℝ) ≤ Y) :
    (∑ n ∈ A, w n) ≤ 2 * Y * ∑ d ∈ D, a d / d := by
  have hbound := sum_le_divisor_majorant N ⌊Y⌋₊ A D w a hA hassign ha
    (fun d hd => ⟨(hD d hd).1, Nat.le_floor (hD d hd).2⟩)
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left (Nat.floor_le hY) (by norm_num)
  · exact Finset.sum_nonneg (fun d hd => div_nonneg (ha d hd) (Nat.cast_nonneg d))

end Problem337.DivisorMoment

end OAI
