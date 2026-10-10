import OAI.NumberTheory.EgyptianFractions.DivisorPrefixCounting
import OAI.NumberTheory.EgyptianFractions.SmallPrimeRankin

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337.DivisorMoment

/-- A constant pointwise bound and a reciprocal sum over admissible prefix
divisors control the corresponding class in a translated short interval. -/
theorem divisor_class_sum_le_exp
    (N : ℕ) (Y R T : ℝ) (A D : Finset ℕ) (w : ℕ → ℝ)
    (hY : 0 ≤ Y) (hA : A ⊆ Finset.Ioc N (N + ⌊Y⌋₊))
    (hassign : ∀ n ∈ A, ∃ d ∈ D, d ∣ n)
    (hweight : ∀ n ∈ A, w n ≤ Real.exp R)
    (hD : ∀ d ∈ D, 0 < d ∧ (d : ℝ) ≤ Y)
    (htail : (∑ d ∈ D, 1 / (d : ℝ)) ≤ Real.exp T) :
    (∑ n ∈ A, w n) ≤ 2 * Y * Real.exp (T + R) := by
  have hbound := sum_le_divisor_majorant_real_cutoff N Y A D w
    (fun _ => Real.exp R) hY hA
    (fun n hn => by
      obtain ⟨d, hd, hdvd⟩ := hassign n hn
      exact ⟨d, hd, hdvd, hweight n hn⟩)
    (fun _ _ => (Real.exp_pos R).le) hD
  have hsum : (∑ d ∈ D, Real.exp R / (d : ℝ)) =
      Real.exp R * ∑ d ∈ D, 1 / (d : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hsum] at hbound
  calc
    (∑ n ∈ A, w n) ≤ 2 * Y * (Real.exp R * ∑ d ∈ D, 1 / (d : ℝ)) := hbound
    _ ≤ 2 * Y * (Real.exp R * Real.exp T) := by
      gcongr
    _ = 2 * Y * Real.exp (T + R) := by
      rw [← Real.exp_add, add_comm R T]

/-- The same bound with the short interval indexed by its displacement h.
No choice or uniqueness of the prefix divisor is required. -/
theorem shifted_divisor_class_sum_le_exp
    (N : ℕ) (Y R T : ℝ) (A D : Finset ℕ) (w : ℕ → ℝ)
    (hY : 0 ≤ Y) (hA : A ⊆ Finset.Icc 1 ⌊Y⌋₊)
    (hassign : ∀ h ∈ A, ∃ d ∈ D, d ∣ N + h)
    (hweight : ∀ h ∈ A, w (N + h) ≤ Real.exp R)
    (hD : ∀ d ∈ D, 0 < d ∧ (d : ℝ) ≤ Y)
    (htail : (∑ d ∈ D, 1 / (d : ℝ)) ≤ Real.exp T) :
    (∑ h ∈ A, w (N + h)) ≤ 2 * Y * Real.exp (T + R) := by
  classical
  let B := A.image (fun h => N + h)
  have hB : B ⊆ Finset.Ioc N (N + ⌊Y⌋₊) := by
    intro n hn
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hh1, hhY⟩ := Finset.mem_Icc.mp (hA hh)
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hsum : (∑ n ∈ B, w n) = ∑ h ∈ A, w (N + h) := by
    apply Finset.sum_image
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  rw [← hsum]
  apply divisor_class_sum_le_exp N Y R T B D w hY hB
  · intro n hn
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
    exact hassign h hh
  · intro n hn
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
    exact hweight h hh
  · exact hD
  · exact htail

/-- The actual small-prime class estimate. The admissible prefixes are
positive divisors at most Y, smooth below P, and larger than exp(v/5).
The exponential saving is uniform in the interval origin, its real length,
the finite class, and the pointwise bound R. -/
theorem small_prime_class_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S v R Y : ℝ), 1 ≤ S → 0 ≤ Y →
      ∀ (N P : ℕ), (P : ℝ) ≤ S ^ (4 : ℕ) + 1 →
      ∀ (A : Finset ℕ) (w : ℕ → ℝ),
      A ⊆ Finset.Ioc N (N + ⌊Y⌋₊) →
      (∀ n ∈ A, w n ≤ Real.exp R) →
      (∀ n ∈ A, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Y ∧ d ∣ n ∧
        d ∈ P.smoothNumbers ∧ Real.exp (v / 5) ≤ (d : ℝ)) →
      (∑ n ∈ A, w n) ≤
        2 * Y * Real.exp (-v / 50 + C * S ^ (2 / 5 : ℝ) + R) := by
  classical
  obtain ⟨C, hC, htail⟩ := small_prime_smooth_tail_bound
  refine ⟨C, hC, ?_⟩
  intro S v R Y hS hY N P hP A w hA hw hpfx
  let D : Finset ℕ := (Finset.Icc 1 ⌊Y⌋₊).filter
    (fun d => d ∈ P.smoothNumbers ∧ Real.exp (v / 5) ≤ (d : ℝ))
  have hD (d : ℕ) (hd : d ∈ D) : 0 < d ∧ (d : ℝ) ≤ Y := by
    have hdI := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
    exact ⟨hdI.1, (by exact_mod_cast hdI.2 : (d : ℝ) ≤ ⌊Y⌋₊).trans
      (Nat.floor_le hY)⟩
  apply divisor_class_sum_le_exp N Y R (-v / 50 + C * S ^ (2 / 5 : ℝ))
    A D w hY hA
  · intro n hn
    obtain ⟨d, hd0, hdY, hdvd, hds, hdlarge⟩ := hpfx n hn
    refine ⟨d, Finset.mem_filter.mpr ⟨?_, hds, hdlarge⟩, hdvd⟩
    exact Finset.mem_Icc.mpr ⟨hd0, Nat.le_floor hdY⟩
  · exact hw
  · exact hD
  · exact htail S v hS P hP D
      (fun d hd => (Finset.mem_filter.mp hd).2.1)
      (fun d hd => (Finset.mem_filter.mp hd).2.2)

/-- Displacement-indexed small-prime class estimate used in the moment sum
over 1 ≤ h ≤ Y. -/
theorem small_prime_class_shifted_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S v R Y : ℝ), 1 ≤ S → 0 ≤ Y →
      ∀ (N P : ℕ), (P : ℝ) ≤ S ^ (4 : ℕ) + 1 →
      ∀ (A : Finset ℕ) (w : ℕ → ℝ), A ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ A, w (N + h) ≤ Real.exp R) →
      (∀ h ∈ A, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Y ∧ d ∣ N + h ∧
        d ∈ P.smoothNumbers ∧ Real.exp (v / 5) ≤ (d : ℝ)) →
      (∑ h ∈ A, w (N + h)) ≤
        2 * Y * Real.exp (-v / 50 + C * S ^ (2 / 5 : ℝ) + R) := by
  classical
  obtain ⟨C, hC, htail⟩ := small_prime_smooth_tail_bound
  refine ⟨C, hC, ?_⟩
  intro S v R Y hS hY N P hP A w hA hw hpfx
  let D : Finset ℕ := (Finset.Icc 1 ⌊Y⌋₊).filter
    (fun d => d ∈ P.smoothNumbers ∧ Real.exp (v / 5) ≤ (d : ℝ))
  have hD (d : ℕ) (hd : d ∈ D) : 0 < d ∧ (d : ℝ) ≤ Y := by
    have hdI := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
    exact ⟨hdI.1, (by exact_mod_cast hdI.2 : (d : ℝ) ≤ ⌊Y⌋₊).trans
      (Nat.floor_le hY)⟩
  apply shifted_divisor_class_sum_le_exp N Y R (-v / 50 + C * S ^ (2 / 5 : ℝ))
    A D w hY hA
  · intro n hn
    obtain ⟨d, hd0, hdY, hdvd, hds, hdlarge⟩ := hpfx n hn
    refine ⟨d, Finset.mem_filter.mpr ⟨?_, hds, hdlarge⟩, hdvd⟩
    exact Finset.mem_Icc.mpr ⟨hd0, Nat.le_floor hdY⟩
  · exact hw
  · exact hD
  · exact htail S v hS P hP D
      (fun d hd => (Finset.mem_filter.mp hd).2.1)
      (fun d hd => (Finset.mem_filter.mp hd).2.2)

end Problem337.DivisorMoment

end

end OAI
