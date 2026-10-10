import OAI.Analysis.IrrationalRotation.Analysis.ModuloIntervalMeasure

namespace OAI

namespace Invariant233.PeriodicIntervalDiscrepancy

open Set MeasureTheory
open scoped ENNReal

theorem length_sub_one_mul_integral_le {f : ℝ → ℝ}
    (hperiod : Function.Periodic f 1) (hf : ∀ x, 0 ≤ f x)
    (hint : IntervalIntegrable f volume 0 1) {a b : ℝ} (hab : a ≤ b) :
    (b - a - 1) * (∫ x in (0 : ℝ)..1, f x) ≤ ∫ x in a..b, f x := by
  let n : ℕ := ⌊b - a⌋₊
  have hn : a + n ≤ b := by
    have := Nat.floor_le (sub_nonneg.mpr hab)
    dsimp [n]
    linarith
  have hn' : b - a - 1 ≤ (n : ℝ) := (Nat.sub_one_lt_floor (b - a)).le
  have hint' := hperiod.intervalIntegrable₀ (by norm_num : (1 : ℝ) ≠ 0) hint
  have hmass : 0 ≤ ∫ x in (0 : ℝ)..1, f x :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) hf
  calc
    (b - a - 1) * (∫ x in (0 : ℝ)..1, f x) ≤
        (n : ℝ) * (∫ x in (0 : ℝ)..1, f x) :=
      mul_le_mul_of_nonneg_right hn' hmass
    _ = ∫ x in a..a + n, f x := by
      have h := hperiod.intervalIntegral_add_zsmul_eq (n : ℤ) a hint'
      simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one,
        hperiod.intervalIntegral_add_eq a 0, zero_add] using h.symm
    _ ≤ ∫ x in a..b, f x :=
      intervalIntegral.integral_mono_interval le_rfl (le_add_of_nonneg_right (Nat.cast_nonneg n)) hn
        (Filter.Eventually.of_forall hf) (hint' _ _)

theorem abs_integral_sub_length_mul_integral_le {f : ℝ → ℝ}
    (hperiod : Function.Periodic f 1) (hint : IntervalIntegrable f volume 0 1)
    {a b : ℝ} (hab : a ≤ b) :
    |(∫ x in a..b, f x) - (b - a) * (∫ x in (0 : ℝ)..1, f x)| ≤
      ∫ x in (0 : ℝ)..1, |f x| := by
  have hperiodAbs : Function.Periodic (fun x => |f x|) 1 := by
    intro x
    change |f (x + 1)| = |f x|
    rw [hperiod x]
  have hp : ∀ x, 0 ≤ |f x| + f x := fun x => by linarith [neg_abs_le (f x)]
  have hm : ∀ x, 0 ≤ |f x| - f x := fun x => sub_nonneg.mpr (le_abs_self (f x))
  have hint' := hperiod.intervalIntegrable₀ (by norm_num : (1 : ℝ) ≠ 0) hint
  have hpu := ModuloIntervalMeasure.integral_periodic_le_length_add_one
    (hperiodAbs.add hperiod) hp (hint.abs.add hint) hab
  have hpl := length_sub_one_mul_integral_le
    (hperiodAbs.add hperiod) hp (hint.abs.add hint) hab
  have hmu := ModuloIntervalMeasure.integral_periodic_le_length_add_one
    (hperiodAbs.sub hperiod) hm (hint.abs.sub hint) hab
  have hml := length_sub_one_mul_integral_le
    (hperiodAbs.sub hperiod) hm (hint.abs.sub hint) hab
  simp only [Pi.add_apply, Pi.sub_apply] at hpu hpl hmu hml
  rw [intervalIntegral.integral_add (hint' a b).abs (hint' a b),
    intervalIntegral.integral_add hint.abs hint] at hpu hpl
  rw [intervalIntegral.integral_sub (hint' a b).abs (hint' a b),
    intervalIntegral.integral_sub hint.abs hint] at hmu hml
  apply abs_le.mpr
  constructor <;> nlinarith

theorem integral_cond_Ioc {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    (∫ x, f x ∂ProbabilityTheory.cond volume (Ioc a b)) =
      (b - a)⁻¹ * ∫ x in a..b, f x := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
    Real.volume_Ioc, ENNReal.toReal_ofReal (sub_pos.mpr hab).le,
    intervalIntegral.integral_of_le hab.le, smul_eq_mul]

theorem abs_integral_cond_sub_integral_le {f : ℝ → ℝ}
    (hperiod : Function.Periodic f 1) (hint : IntervalIntegrable f volume 0 1)
    {a b : ℝ} (hab : a < b) :
    |(∫ x, f x ∂ProbabilityTheory.cond volume (Ioc a b)) -
        (∫ x in (0 : ℝ)..1, f x)| ≤
      (b - a)⁻¹ * ∫ x in (0 : ℝ)..1, |f x| := by
  have hlen : 0 < b - a := sub_pos.mpr hab
  rw [integral_cond_Ioc hab]
  calc
    |(b - a)⁻¹ * (∫ x in a..b, f x) - (∫ x in (0 : ℝ)..1, f x)| =
        (b - a)⁻¹ * |(∫ x in a..b, f x) -
          (b - a) * (∫ x in (0 : ℝ)..1, f x)| := by
      have heq : (b - a)⁻¹ * (∫ x in a..b, f x) - (∫ x in (0 : ℝ)..1, f x) =
          (b - a)⁻¹ * ((∫ x in a..b, f x) -
            (b - a) * (∫ x in (0 : ℝ)..1, f x)) := by
        rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hlen.ne', one_mul]
      rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hlen)]
    _ ≤ (b - a)⁻¹ * ∫ x in (0 : ℝ)..1, |f x| :=
      mul_le_mul_of_nonneg_left
        (abs_integral_sub_length_mul_integral_le hperiod hint hab.le)
        (inv_nonneg.mpr hlen.le)

theorem cond_fract_preimage_ge {s : Set ℝ} (hs : MeasurableSet s)
    {a b : ℝ} (hab : a < b) :
    (1 - 1 / (b - a)) * volume.real (s ∩ Ico 0 1) ≤
      (ProbabilityTheory.cond volume (Ioc a b)).real (Int.fract ⁻¹' s) := by
  have hr : 0 < b - a := sub_pos.mpr hab
  have hs' : MeasurableSet (Int.fract ⁻¹' s) := hs.preimage measurable_fract
  have hnonneg : ∀ x, 0 ≤ (Int.fract ⁻¹' s).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have h := length_sub_one_mul_integral_le
    (ModuloIntervalMeasure.periodic_fract_indicator s) hnonneg
    (ModuloIntervalMeasure.intervalIntegrable_indicator_one hs' 0 1) hab.le
  rw [ModuloIntervalMeasure.integral_fract_indicator_one_period hs,
    intervalIntegral.integral_of_le hab.le, integral_indicator_const 1 hs',
    measureReal_restrict_apply hs'] at h
  simp only [smul_eq_mul, mul_one] at h
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hr.le)
  rw [ProbabilityTheory.cond, measureReal_ennreal_smul_apply,
    measureReal_restrict_apply hs', ENNReal.toReal_inv, Real.volume_Ioc,
    ENNReal.toReal_ofReal hr.le]
  calc
    (1 - 1 / (b - a)) * volume.real (s ∩ Ico 0 1) =
        (b - a)⁻¹ * ((b - a - 1) * volume.real (s ∩ Ico 0 1)) := by
      rw [← mul_assoc, mul_sub, inv_mul_cancel₀ hr.ne', mul_one, one_div]
    _ ≤ _ := hh

theorem fract_comp_eqOn {E : Type*} (g : ℝ → E) :
    EqOn (fun x => g (Int.fract x)) g (Ioo 0 1) := by
  intro x hx
  change g (Int.fract x) = g x
  rw [Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩]

theorem intervalIntegrable_fract_comp {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 1) :
    IntervalIntegrable (fun x => g (Int.fract x)) volume 0 1 := by
  apply hg.congr_uIoo
  simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using (fract_comp_eqOn g).symm

theorem integral_cond_Ioc_mul {f : ℝ → ℝ} {a b k : ℝ}
    (hab : a < b) (hk : 0 < k) :
    (∫ x, f (k * x) ∂ProbabilityTheory.cond volume (Ioc a b)) =
      ∫ x, f x ∂ProbabilityTheory.cond volume (Ioc (k * a) (k * b)) := by
  rw [integral_cond_Ioc hab, integral_cond_Ioc (mul_lt_mul_of_pos_left hab hk),
    intervalIntegral.integral_comp_mul_left f hk.ne', smul_eq_mul]
  rw [← mul_sub, mul_inv_rev, mul_assoc]

theorem uniform_angle_test_le {N n : ℝ} (hN : 0 < N) (hn : 0 < n)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 1) :
    |(∫ θ, g (Int.fract (n * θ))
        ∂ProbabilityTheory.cond volume (Icc (1 / N) (2 / N))) -
      (∫ t in (0 : ℝ)..1, g t)| ≤ (N / n) * ∫ t in (0 : ℝ)..1, |g t| := by
  have hab : (1 : ℝ) / N < 2 / N :=
    (div_lt_div_iff_of_pos_right hN).mpr (by norm_num)
  have hperiod : Function.Periodic (fun x => g (Int.fract x)) 1 := by
    intro x
    simp only [Int.fract_add_one]
  have h := abs_integral_cond_sub_integral_le hperiod
    (intervalIntegrable_fract_comp hg) (mul_lt_mul_of_pos_left hab hn)
  have hmean : (∫ t in (0 : ℝ)..1, g (Int.fract t)) = ∫ t in (0 : ℝ)..1, g t :=
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fract_comp_eqOn g)
  have habs : (∫ t in (0 : ℝ)..1, |g (Int.fract t)|) =
      ∫ t in (0 : ℝ)..1, |g t| :=
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fract_comp_eqOn (fun t => |g t|))
  have hlen : (n * (2 / N) - n * (1 / N))⁻¹ = N / n := by
    rw [← mul_sub, ← sub_div, show (2 : ℝ) - 1 = 1 by norm_num]
    field_simp
  rw [hmean, habs, hlen] at h
  rw [ModuloIntervalMeasure.cond_Icc_eq_cond_Ioc,
    integral_cond_Ioc_mul (f := fun x => g (Int.fract x)) hab hn]
  exact h

end Invariant233.PeriodicIntervalDiscrepancy

end OAI
