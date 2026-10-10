import OAI.NumberTheory.Ostmann.ZeroDensity.GiantDensitySum

namespace OAI

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem norm_harmonic_pair_integral_le (u v r s C : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (huv : u ≤ v) (hrs : r ≤ s) (hv : v ≤ u + 1) (hs : s ≤ r + 1)
    (hC : 0 ≤ C) (F : ℝ → ℝ → ℂ)
    (hF : ∀ x ∈ Set.Ioc u v, ∀ y ∈ Set.Ioc r s, ‖F x y‖ ≤ C) :
    ‖∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
      F x y / ((x : ℂ) * (y : ℂ))‖ ≤ C / (u * r) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hpoint (x : ℝ) (hx : x ∈ Set.Ioc u v) (y : ℝ) (hy : y ∈ Set.Ioc r s) :
      ‖F x y / ((x : ℂ) * (y : ℂ))‖ ≤ C / (u * r) := by
    have hx0 := hu0.trans hx.1
    have hy0 := hr0.trans hy.1
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx0, abs_of_pos hy0]
    exact (div_le_div_of_nonneg_right (hF x hx y hy) (mul_nonneg hx0.le hy0.le)).trans
      (div_le_div_of_nonneg_left hC (mul_pos hu0 hr0)
        (mul_le_mul hx.1.le hy.1.le hr0.le hx0.le))
  have hin (x : ℝ) (hx : x ∈ Set.Ioc u v) :=
    norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top (hpoint x hx)
  simp only [Real.volume_real_Ioc_of_le hrs] at hin
  have hout := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top hin
  rw [Real.volume_real_Ioc_of_le huv] at hout
  calc
    _ ≤ (C / (u * r) * (s - r)) * (v - u) := hout
    _ ≤ C / (u * r) * 1 * 1 := by gcongr <;> linarith
    _ = _ := by ring

/-- A finite signed average is integrated before its norm is bounded. This
retains cancellation in the arithmetic coefficient on each giant cell. -/
theorem finite_harmonic_pair_sum_norm {A : Type*} [Fintype A]
    (u v r s C : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (huv : u ≤ v) (hrs : r ≤ s) (hv : v ≤ u + 1) (hs : s ≤ r + 1)
    (hC : 0 ≤ C) (w : A → ℂ) (F : A → ℝ → ℝ → ℂ)
    (hmeas : ∀ a, Measurable (Function.uncurry (F a)))
    (K : A → ℝ) (hK : ∀ a, 0 ≤ K a)
    (hbound : ∀ a x, x ∈ Set.Ioc u v → ∀ y, y ∈ Set.Ioc r s → ‖F a x y‖ ≤ K a)
    (hmean : ∀ x ∈ Set.Ioc u v, ∀ y ∈ Set.Ioc r s, ‖∑ a, w a * F a x y‖ ≤ C) :
    ‖∑ a, w a * ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
      F a x y / ((x : ℂ) * (y : ℂ))‖ ≤ C / (u * r) := by
  let box := Set.Ioc u v ×ˢ Set.Ioc r s
  let H := fun a (z : ℝ × ℝ) => box.indicator
    (fun z => w a * F a z.1 z.2 / ((z.1 : ℂ) * (z.2 : ℂ))) z
  have hH (a : A) : Measurable (H a) := by
    apply Measurable.indicator _ (measurableSet_Ioc.prod measurableSet_Ioc)
    exact (measurable_const.mul (hmeas a)).div
      ((Complex.continuous_ofReal.measurable.comp measurable_fst).mul
        (Complex.continuous_ofReal.measurable.comp measurable_snd))
  have hnorm (a : A) (z : ℝ × ℝ) : ‖H a z‖ ≤ ‖w a‖ * K a / (u * r) := by
    by_cases hz : z ∈ box
    · obtain ⟨hx, hy⟩ := hz
      have hx0 : 0 < z.1 := (lt_of_lt_of_le zero_lt_one hu).trans hx.1
      have hy0 : 0 < z.2 := (lt_of_lt_of_le zero_lt_one hr).trans hy.1
      simp only [H, Set.indicator_of_mem (show z ∈ box from ⟨hx, hy⟩), norm_div,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, abs_of_pos hy0]
      exact (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbound a z.1 hx z.2 hy) (norm_nonneg _))
        (mul_nonneg hx0.le hy0.le)).trans
        (div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (hK a)) (by positivity)
          (mul_le_mul hx.1.le hy.1.le (by linarith) hx0.le))
    · rw [show H a z = 0 from Set.indicator_of_notMem hz _]
      simp only [norm_zero]
      exact div_nonneg (mul_nonneg (norm_nonneg _) (hK a)) (by linarith [mul_pos (lt_of_lt_of_le zero_lt_one hu) (lt_of_lt_of_le zero_lt_one hr)])
  let μ := volume.restrict (Set.Ioc u v)
  let ν := volume.restrict (Set.Ioc r s)
  have hp (a : A) : Integrable (H a) (μ.prod ν) :=
    ⟨(hH a).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (hnorm a))⟩
  have hi (a : A) (x : ℝ) : Integrable (fun y => H a (x, y)) ν :=
    ⟨((hH a).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun y => hnorm a (x, y)))⟩
  have hswap := double_integral_finset_sum (Finset.univ : Finset A) μ ν
    (fun a x y => H a (x, y)) (fun a _ => hi a) (fun a _ => (hp a).integral_prod_left)
  have heq (a : A) : (∫ x, ∫ y, H a (x, y) ∂ν ∂μ) =
      w a * ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
        F a x y / ((x : ℂ) * (y : ℂ)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    simp only [H, box, Set.indicator_of_mem (show (x, y) ∈ box from ⟨hx, hy⟩)]
    ring
  have hinside : (∫ x, ∫ y, ∑ a, H a (x, y) ∂ν ∂μ) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
        (∑ a, w a * F a x y) / ((x : ℂ) * (y : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    simp only [H, box, Set.indicator_of_mem (show (x, y) ∈ box from ⟨hx, hy⟩),
      Finset.sum_div]
  simp only [heq] at hswap
  rw [← hswap, hinside]
  exact norm_harmonic_pair_integral_le u v r s C hu hr huv hrs hv hs hC _ hmean

end Ostmann

end OAI
