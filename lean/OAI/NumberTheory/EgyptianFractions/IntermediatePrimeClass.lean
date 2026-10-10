import OAI.NumberTheory.EgyptianFractions.DivisorPrefixCounting
import OAI.NumberTheory.EgyptianFractions.RankinBand

namespace OAI
open scoped BigOperators

namespace Problem337.DivisorMoment

/-- Prefix counting in the shift convention used by short-interval moments. -/
theorem sum_le_shifted_divisor_majorant_real_cutoff
    (N : ℕ) (Y : ℝ) (H D : Finset ℕ) (w a : ℕ → ℝ) (hY : 0 ≤ Y)
    (hH : H ⊆ Finset.Icc 1 ⌊Y⌋₊)
    (hassign : ∀ h ∈ H, ∃ d ∈ D, d ∣ N + h ∧ w h ≤ a d)
    (ha : ∀ d ∈ D, 0 ≤ a d)
    (hD : ∀ d ∈ D, 0 < d ∧ (d : ℝ) ≤ Y) :
    (∑ h ∈ H, w h) ≤ 2 * Y * ∑ d ∈ D, a d / d := by
  classical
  let A := H.image (fun h => N + h)
  have hA : A ⊆ Finset.Ioc N (N + ⌊Y⌋₊) := by
    intro n hn
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hh1, hhY⟩ := Finset.mem_Icc.mp (hH hh)
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hassignA : ∀ n ∈ A, ∃ d ∈ D, d ∣ n ∧ w (n - N) ≤ a d := by
    intro n hn
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
    simpa only [Nat.add_sub_cancel_left] using hassign h hh
  have hsum : (∑ n ∈ A, w (n - N)) = ∑ h ∈ H, w h := by
    dsimp [A]
    rw [Finset.sum_image (fun a _ b _ h => Nat.add_left_cancel h)]
    simp only [Nat.add_sub_cancel_left]
  have h := sum_le_divisor_majorant_real_cutoff N Y A D (fun n => w (n - N)) a
    hY hA hassignA ha hD
  rwa [hsum] at h

/-- One actual intermediate-prime class, with all divisor-prefix counting and
smooth Rankin summation performed. Only the pointwise prefix witnesses remain
as hypotheses; no moment or counting estimate is assumed. -/
theorem intermediate_prime_class_bound (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (Y v t R : ℝ) (H : Finset ℕ) (w : ℕ → ℝ),
      0 ≤ Y → 1 ≤ t → t ≤ v → Real.log (v / t) / (10 * t) ≤ 1 / 4 →
      H ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ H, ∃ d : ℕ, d ∣ N + h ∧ (d : ℝ) ≤ Y ∧
        Real.exp (v / 5) ≤ (d : ℝ) ∧
        (∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) ≤ Real.exp (2 * t)) ∧
        w h ≤ Real.exp R * (d.divisors.card : ℝ) ^ r) →
      (∑ h ∈ H, w h) ≤ 2 * Y *
        Real.exp (R - (v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  classical
  obtain ⟨C, hC, hRankin⟩ := Problem337.divisor_rankin_intermediate_band r
  refine ⟨C, hC, ?_⟩
  intro N Y v t R H w hY ht htv hβ hH hprefix
  let K : ℕ := ⌊Real.exp (2 * t)⌋₊ + 1
  let D : Finset ℕ := (Finset.Icc 1 ⌊Y⌋₊).filter
    (fun d => Real.exp (v / 5) ≤ (d : ℝ) ∧ d ∈ K.smoothNumbers)
  have hK : ∀ p ∈ K.primesBelow, (p : ℝ) ≤ Real.exp (2 * t) := by
    intro p hp
    have hpK := Nat.lt_of_mem_primesBelow hp
    have hpFloor : p ≤ ⌊Real.exp (2 * t)⌋₊ := by dsimp [K] at hpK; omega
    exact (Nat.cast_le.mpr hpFloor).trans (Nat.floor_le (Real.exp_pos _).le)
  have hD : ∀ d ∈ D, 0 < d ∧ (d : ℝ) ≤ Y := by
    intro d hd
    have hdI := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
    exact ⟨by omega, (Nat.cast_le.mpr hdI.2).trans (Nat.floor_le hY)⟩
  have hassign : ∀ h ∈ H, ∃ d ∈ D, d ∣ N + h ∧
      w h ≤ Real.exp R * (d.divisors.card : ℝ) ^ r := by
    intro h hh
    obtain ⟨d, hdvd, hdY, hdlarge, hdprime, hdw⟩ := hprefix h hh
    have hdposR : (0 : ℝ) < d := (Real.exp_pos _).trans_le hdlarge
    have hdpos : 0 < d := by exact_mod_cast hdposR
    refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨by omega, Nat.le_floor hdY⟩, hdlarge, ?_⟩, hdvd, hdw⟩
    apply Nat.mem_smoothNumbers'.mpr
    intro p hp hpd
    have hpFloor : p ≤ ⌊Real.exp (2 * t)⌋₊ := Nat.le_floor (hdprime p hp hpd)
    dsimp [K]
    omega
  have hcount := sum_le_shifted_divisor_majorant_real_cutoff N Y H D w
    (fun d => Real.exp R * (d.divisors.card : ℝ) ^ r) hY hH hassign
    (fun d _ => by positivity) hD
  have hrank := hRankin v t ht htv hβ K hK D
    (fun d hd => (Finset.mem_filter.mp hd).2.2)
    (fun d hd => (Finset.mem_filter.mp hd).2.1)
  calc
    (∑ h ∈ H, w h) ≤ 2 * Y *
        ∑ d ∈ D, (Real.exp R * (d.divisors.card : ℝ) ^ r) / d := hcount
    _ = 2 * Y * (Real.exp R * ∑ d ∈ D, (d.divisors.card : ℝ) ^ r / d) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 2 * Y * (Real.exp R * Real.exp (-(v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrank (Real.exp_pos _).le)
        (by positivity)
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- The same evaluated class estimate for arbitrary real moment orders. -/
theorem intermediate_prime_class_bound_real (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (Y v t R : ℝ) (H : Finset ℕ) (w : ℕ → ℝ),
      0 ≤ Y → 1 ≤ t → t ≤ v → Real.log (v / t) / (10 * t) ≤ 1 / 4 →
      H ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ H, ∃ d : ℕ, d ∣ N + h ∧ (d : ℝ) ≤ Y ∧
        Real.exp (v / 5) ≤ (d : ℝ) ∧
        (∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) ≤ Real.exp (2 * t)) ∧
        w h ≤ Real.exp R * (d.divisors.card : ℝ) ^ r) →
      (∑ h ∈ H, w h) ≤ 2 * Y *
        Real.exp (R - (v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  obtain ⟨C, hC, hbound⟩ := intermediate_prime_class_bound ⌈r⌉₊
  refine ⟨C, hC, ?_⟩
  intro N Y v t R H w hY ht htv hβ hH hprefix
  apply hbound N Y v t R H w hY ht htv hβ hH
  intro h hh
  obtain ⟨d, hdvd, hdY, hdlarge, hdprime, hdw⟩ := hprefix h hh
  refine ⟨d, hdvd, hdY, hdlarge, hdprime, hdw.trans ?_⟩
  have hdposR : (0 : ℝ) < d := (Real.exp_pos _).trans_le hdlarge
  have hdne : d ≠ 0 := by exact_mod_cast (ne_of_gt hdposR)
  have hcard : (1 : ℝ) ≤ d.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hdne⟩
  have hpow := Real.rpow_le_rpow_of_exponent_le hcard (Nat.le_ceil r)
  rw [Real.rpow_natCast] at hpow
  exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le

/-- The prefix cutoff `sqrt Y` used in the actual prime-factor decomposition
is directly admissible. The arbitrary loss `R` can be instantiated by `r*B*v/t`. -/
theorem intermediate_prime_class_sqrt_bound (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (Y v t R : ℝ) (H : Finset ℕ) (w : ℕ → ℝ),
      1 ≤ Y → 1 ≤ t → t ≤ v → Real.log (v / t) / (10 * t) ≤ 1 / 4 →
      H ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ H, ∃ d : ℕ, d ∣ N + h ∧ (d : ℝ) ≤ Real.sqrt Y ∧
        Real.exp (v / 5) ≤ (d : ℝ) ∧
        (∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) ≤ Real.exp (2 * t)) ∧
        w h ≤ Real.exp R * (d.divisors.card : ℝ) ^ r) →
      (∑ h ∈ H, w h) ≤ 2 * Y *
        Real.exp (R - (v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  obtain ⟨C, hC, hbound⟩ := intermediate_prime_class_bound_real r
  refine ⟨C, hC, ?_⟩
  intro N Y v t R H w hY ht htv hβ hH hprefix
  apply hbound N Y v t R H w (by linarith) ht htv hβ hH
  intro h hh
  obtain ⟨d, hdvd, hdY, hdlarge, hdprime, hdw⟩ := hprefix h hh
  exact ⟨d, hdvd, hdY.trans (Real.sqrt_le_self_iff.mpr (Or.inr hY)),
    hdlarge, hdprime, hdw⟩

end Problem337.DivisorMoment

end OAI
