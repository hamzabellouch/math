import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeJointContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # Inhomogeneous evolution on the exact whole-space homogeneous space -/

open MeasureTheory Set

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

noncomputable def homogeneousDuhamel (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (t : ℝ) (r : ℝ → HomogeneousY a k) : HomogeneousY a k :=
  ∫ τ in (0 : ℝ)..t, homogeneousFreeOperator a b k (t - τ) ha ha1 hk (r τ)

theorem continuousOn_homogeneousDuhamelIntegrand (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (t : ℝ) (r : ℝ → HomogeneousY a k) (hr : ContinuousOn r (Icc 0 t)) :
    ContinuousOn (fun τ => homogeneousFreeOperator a b k (t - τ) ha ha1 hk (r τ))
      (Icc 0 t) :=
  (continuous_homogeneousFreeOperator_uncurry a b k ha ha1 hk).continuousOn.comp
    ((continuous_const.sub continuous_id).continuousOn.prodMk hr) (fun _ _ => mem_univ _)

theorem homogeneousDuhamel_norm_le (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (t : ℝ) (ht : 0 ≤ t) (r : ℝ → HomogeneousY a k) (hr : ContinuousOn r (Icc 0 t)) :
    ‖homogeneousDuhamel a b k ha ha1 hk t r‖ ≤
      ∫ τ in Icc 0 t, Real.exp (-a * (t - τ) / 2) * ‖r τ‖ := by
  rw [homogeneousDuhamel, intervalIntegral.integral_of_le ht,
    ← integral_Icc_eq_integral_Ioc]
  have hg : IntegrableOn (fun τ => Real.exp (-a * (t - τ) / 2) * ‖r τ‖) (Icc 0 t) :=
    ((Real.continuous_exp.comp (by fun_prop)).continuousOn.mul hr.norm).integrableOn_compact
      isCompact_Icc
  apply norm_integral_le_of_norm_le hg
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  exact homogeneousFreeOperator_forward_bound a b k (t - τ) ha ha1 hk
    (sub_nonneg.mpr hτ.2) (r τ)

theorem homogeneousDuhamel_sub (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (t : ℝ) (ht : 0 ≤ t) (r q : ℝ → HomogeneousY a k)
    (hr : ContinuousOn r (Icc 0 t)) (hq : ContinuousOn q (Icc 0 t)) :
    homogeneousDuhamel a b k ha ha1 hk t (fun τ => r τ - q τ) =
      homogeneousDuhamel a b k ha ha1 hk t r - homogeneousDuhamel a b k ha ha1 hk t q := by
  have hir := (continuousOn_homogeneousDuhamelIntegrand a b k ha ha1 hk t r hr).intervalIntegrable_of_Icc (μ := volume)
    ht
  have hiq := (continuousOn_homogeneousDuhamelIntegrand a b k ha ha1 hk t q hq).intervalIntegrable_of_Icc (μ := volume)
    ht
  unfold homogeneousDuhamel
  simp only [map_sub]
  exact intervalIntegral.integral_sub hir hiq

theorem homogeneousDuhamel_norm_le_mul (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (t C : ℝ) (ht : 0 ≤ t) (r : ℝ → HomogeneousY a k)
    (hbound : ∀ τ ∈ Icc 0 t, ‖r τ‖ ≤ C) :
    ‖homogeneousDuhamel a b k ha ha1 hk t r‖ ≤ t * C := by
  rw [homogeneousDuhamel, intervalIntegral.integral_of_le ht,
    ← integral_Icc_eq_integral_Ioc]
  have hpoint (τ : ℝ) (hτ : τ ∈ Icc 0 t) :
      ‖homogeneousFreeOperator a b k (t - τ) ha ha1 hk (r τ)‖ ≤ C := by
    apply (homogeneousFreeOperator_forward_bound a b k (t - τ) ha ha1 hk
      (sub_nonneg.mpr hτ.2) (r τ)).trans
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by
      nlinarith [hτ.2]))).trans (hbound τ hτ)
  have h := norm_integral_le_of_norm_le
    (f := fun τ => homogeneousFreeOperator a b k (t - τ) ha ha1 hk (r τ))
    (μ := volume.restrict (Icc 0 t)) (g := fun _ => C)
    (integrableOn_const isCompact_Icc.measure_ne_top)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ; exact hpoint τ hτ)
  simpa only [setIntegral_const, Real.volume_real_Icc_of_le ht, sub_zero, smul_eq_mul] using h

/-- Unit-interval rescaling keeps continuity valid for positive and negative time. -/
theorem homogeneousDuhamel_eq_unitIntegral (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (t : ℝ) (r : ℝ → HomogeneousY a k) :
    homogeneousDuhamel a b k ha ha1 hk t r =
      t • ∫ u in Icc (0 : ℝ) 1,
        homogeneousFreeOperator a b k (t - t * u) ha ha1 hk (r (t * u)) := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (a := 0) (b := 1)
    (fun τ => homogeneousFreeOperator a b k (t - τ) ha ha1 hk (r τ)) t
  simpa only [mul_zero, mul_one, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc, homogeneousDuhamel] using h.symm

theorem continuous_homogeneousDuhamel (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (r : ℝ → HomogeneousY a k) (hr : Continuous r) :
    Continuous (fun t => homogeneousDuhamel a b k ha ha1 hk t r) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      homogeneousFreeOperator a b k (p.1 - p.1 * p.2) ha ha1 hk (r (p.1 * p.2))) :=
    (continuous_homogeneousFreeOperator_uncurry a b k ha ha1 hk).comp
      ((continuous_fst.sub (continuous_fst.mul continuous_snd)).prodMk
        (hr.comp (continuous_fst.mul continuous_snd)))
  simp only [homogeneousDuhamel_eq_unitIntegral]
  exact continuous_id.smul (continuous_parametric_integral_of_continuous hc isCompact_Icc)

end DefocusingNLS

end OAI
