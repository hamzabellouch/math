import OAI.NumberTheory.Ostmann.Arithmetic.HarmonicPairIntegral

namespace OAI

/-! # Finite signed averages under the original external integer density -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem finite_mixed_pair_sum_norm {A : Type*} [Fintype A]
    (u v r s center C : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (huv : u ≤ v) (hrs : r ≤ s) (hv : v ≤ u + 1) (hs : s ≤ r + 1)
    (hcenter : v ≤ center + 1) (hC : 0 ≤ C) (w : A → ℂ)
    (F : A → ℝ → ℝ → ℂ) (hmeas : ∀ a, Measurable (Function.uncurry (F a)))
    (K : A → ℝ) (hK : ∀ a, 0 ≤ K a)
    (hbound : ∀ a x, x ∈ Set.Ioc u v → ∀ y, y ∈ Set.Ioc r s → ‖F a x y‖ ≤ K a)
    (hmean : ∀ x ∈ Set.Ioc u v, ∀ y ∈ Set.Ioc r s, ‖∑ a, w a * F a x y‖ ≤ C) :
    ‖∑ a, w a * ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
      F a x y * (Real.exp (x - center) : ℂ) / (y : ℂ)‖ ≤
      (2 * Real.exp 1 * C) / r := by
  let F' := fun a x y => ((x * Real.exp (x - center) : ℝ) : ℂ) * F a x y
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hv0 : 0 ≤ v := hu0.le.trans huv
  have he (x : ℝ) (hx : x ∈ Set.Ioc u v) :
      0 ≤ x * Real.exp (x - center) ∧ x * Real.exp (x - center) ≤ v * Real.exp 1 := by
    have hx0 : 0 ≤ x := hu0.le.trans hx.1.le
    refine ⟨mul_nonneg hx0 (Real.exp_nonneg _), ?_⟩
    exact mul_le_mul hx.2 (Real.exp_le_exp.mpr (by linarith [hx.2]))
      (Real.exp_nonneg _) hv0
  have hm (a : A) : Measurable (Function.uncurry (F' a)) := by
    have hscalar : Measurable (fun z : ℝ × ℝ => ((z.1 * Real.exp (z.1 - center) : ℝ) : ℂ)) := by
      fun_prop
    exact hscalar.mul (hmeas a)
  have hpoint (a : A) (x : ℝ) (hx : x ∈ Set.Ioc u v) (y : ℝ) (hy : y ∈ Set.Ioc r s) :
      ‖F' a x y‖ ≤ (v * Real.exp 1) * K a := by
    dsimp only [F']
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (he x hx).1]
    exact mul_le_mul (he x hx).2 (hbound a x hx y hy) (norm_nonneg _) (by positivity)
  have hmean' (x : ℝ) (hx : x ∈ Set.Ioc u v) (y : ℝ) (hy : y ∈ Set.Ioc r s) :
      ‖∑ a, w a * F' a x y‖ ≤ v * Real.exp 1 * C := by
    have hh : (∑ a, w a * F' a x y) =
        ((x * Real.exp (x - center) : ℝ) : ℂ) * ∑ a, w a * F a x y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [F']
      ring
    rw [hh, norm_mul, Complex.norm_real, Real.norm_of_nonneg (he x hx).1]
    exact mul_le_mul (he x hx).2 (hmean x hx y hy) (norm_nonneg _) (by positivity)
  have hh := finite_harmonic_pair_sum_norm u v r s (v * Real.exp 1 * C)
    hu hr huv hrs hv hs (by positivity) w F' hm
    (fun a => (v * Real.exp 1) * K a) (fun a => mul_nonneg (by positivity) (hK a))
    hpoint hmean'
  have heq (a : A) : (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
      F a x y * (Real.exp (x - center) : ℂ) / (y : ℂ)) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s, F' a x y / ((x : ℂ) * (y : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hu0.trans hx.1)
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hr0.trans hy.1)
    dsimp only [F']
    push_cast
    field_simp
  simp_rw [heq]
  apply hh.trans
  have hratio : v / u ≤ 2 := (div_le_iff₀ hu0).mpr (by linarith)
  calc
    v * Real.exp 1 * C / (u * r) = (v / u) * (Real.exp 1 * C / r) := by ring
    _ ≤ 2 * (Real.exp 1 * C / r) :=
      mul_le_mul_of_nonneg_right hratio (div_nonneg (mul_nonneg (Real.exp_nonneg _) hC) hr0.le)
    _ = _ := by ring

end Ostmann

end OAI
