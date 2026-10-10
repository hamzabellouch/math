import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFreeContinuity
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # Inhomogeneous propagation in the exact expanding Sobolev norms

The forcing at time `τ` is represented in `Y_(L exp(τ/2))`.  Its free transport
therefore lands in the same final space `Y_(L exp(t/2))` for every `τ ∈ [0,t]`.
The estimate keeps the exact exponential kernel and is uniform in `L ≥ 1`.
-/

open MeasureTheory Set

namespace DefocusingNLS

noncomputable def expandingDuhamelIntegrand (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (t : ℝ) (r : ℝ → FourierL2) (τ : ℝ) : FourierL2 :=
  if h : τ ∈ Icc 0 t then
    expandingFreeStep a b k (expandingRadius L τ) (t - τ) ha hk
      (hL.trans (expandingRadius_ge L τ hL h.1)) (sub_nonneg.mpr h.2) (r τ)
  else 0

noncomputable def expandingDuhamel (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (t : ℝ) (r : ℝ → FourierL2) : FourierL2 :=
  ∫ τ in Icc 0 t, expandingDuhamelIntegrand a b k L ha hk hL t r τ

@[simp] theorem expandingDuhamelIntegrand_of_mem (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (t : ℝ) (r : ℝ → FourierL2) (τ : ℝ) (hτ : τ ∈ Icc 0 t) :
    expandingDuhamelIntegrand a b k L ha hk hL t r τ =
      expandingFreeStep a b k (expandingRadius L τ) (t - τ) ha hk
        (hL.trans (expandingRadius_ge L τ hL hτ.1)) (sub_nonneg.mpr hτ.2) (r τ) := by
  simp only [expandingDuhamelIntegrand, dite_eq_left hτ]

/-- Every forcing time is transported into the prescribed final expanding torus. -/
theorem expandingDuhamel_destination (L t τ : ℝ) :
    expandingRadius (expandingRadius L τ) (t - τ) = expandingRadius L t := by
  rw [expandingRadius_add]
  congr 1
  ring

theorem continuousOn_expandingDuhamelIntegrand (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (t : ℝ) (r : ℝ → FourierL2) (hr : ContinuousOn r (Icc 0 t)) :
    ContinuousOn (expandingDuhamelIntegrand a b k L ha hk hL t r) (Icc 0 t) := by
  let p : Icc (0 : ℝ) t → ExpandingFreeParameters := fun τ =>
    (⟨expandingRadius L τ, hL.trans (expandingRadius_ge L τ hL τ.2.1)⟩,
      ⟨t - τ, sub_nonneg.mpr τ.2.2⟩)
  have hp : Continuous p := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      unfold expandingRadius
      exact continuous_const.mul (Real.continuous_exp.comp (continuous_subtype_val.div_const 2))
    · apply Continuous.subtype_mk
      exact continuous_const.sub continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  convert (continuous_expandingFreeFamily_uncurry a b k ha hk).comp
    (hp.prodMk hr.domRestrict) using 1
  ext τ
  simp only [domRestrict_apply, expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ τ.2]
  rfl

theorem integrableOn_expandingDuhamelIntegrand (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (t : ℝ) (r : ℝ → FourierL2) (hr : ContinuousOn r (Icc 0 t)) :
    IntegrableOn (expandingDuhamelIntegrand a b k L ha hk hL t r) (Icc 0 t) :=
  (continuousOn_expandingDuhamelIntegrand a b k L ha hk hL t r hr).integrableOn_compact isCompact_Icc

/-- Variation of constants has the manuscript's `exp(-a (t-τ)/2)` bound. -/
theorem expandingDuhamel_norm_le (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (t : ℝ) (r : ℝ → FourierL2) (hr : ContinuousOn r (Icc 0 t)) :
    ‖expandingDuhamel a b k L ha hk hL t r‖ ≤
      ∫ τ in Icc 0 t, Real.exp (-a * (t - τ) / 2) * ‖r τ‖ := by
  have hg : IntegrableOn (fun τ => Real.exp (-a * (t - τ) / 2) * ‖r τ‖) (Icc 0 t) :=
    ((Real.continuous_exp.comp (by fun_prop)).continuousOn.mul hr.norm).integrableOn_compact
      isCompact_Icc
  apply norm_integral_le_of_norm_le hg
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  rw [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ]
  exact expandingFreeStep_norm_bound a b k (expandingRadius L τ) (t - τ) ha hk
    (hL.trans (expandingRadius_ge L τ hL hτ.1)) (sub_nonneg.mpr hτ.2) (r τ)

/-- The inhomogeneous operator is linear in continuous forcing histories. -/
theorem expandingDuhamel_sub (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (t : ℝ) (r q : ℝ → FourierL2)
    (hr : ContinuousOn r (Icc 0 t)) (hq : ContinuousOn q (Icc 0 t)) :
    expandingDuhamel a b k L ha hk hL t (fun τ => r τ - q τ) =
      expandingDuhamel a b k L ha hk hL t r - expandingDuhamel a b k L ha hk hL t q := by
  unfold expandingDuhamel
  rw [← integral_sub (integrableOn_expandingDuhamelIntegrand a b k L ha hk hL t r hr)
    (integrableOn_expandingDuhamelIntegrand a b k L ha hk hL t q hq)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  simp only [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ, map_sub]

/-- The same exponential kernel controls perturbations of the forcing history. -/
theorem expandingDuhamel_sub_norm_le (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (t : ℝ) (r q : ℝ → FourierL2)
    (hr : ContinuousOn r (Icc 0 t)) (hq : ContinuousOn q (Icc 0 t)) :
    ‖expandingDuhamel a b k L ha hk hL t r - expandingDuhamel a b k L ha hk hL t q‖ ≤
      ∫ τ in Icc 0 t, Real.exp (-a * (t - τ) / 2) * ‖r τ - q τ‖ := by
  rw [← expandingDuhamel_sub a b k L ha hk hL t r q hr hq]
  exact expandingDuhamel_norm_le a b k L ha hk hL t (fun τ => r τ - q τ) (hr.sub hq)

/-- A bounded forcing gives a scale-independent short-time estimate. -/
theorem expandingDuhamel_norm_le_mul (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (t C : ℝ) (ht : 0 ≤ t) (r : ℝ → FourierL2)
    (hr : ContinuousOn r (Icc 0 t)) (hbound : ∀ τ ∈ Icc 0 t, ‖r τ‖ ≤ C) :
    ‖expandingDuhamel a b k L ha hk hL t r‖ ≤ t * C := by
  have _hi := integrableOn_expandingDuhamelIntegrand a b k L ha hk hL t r hr
  have hpoint (τ : ℝ) (hτ : τ ∈ Icc 0 t) :
      ‖expandingDuhamelIntegrand a b k L ha hk hL t r τ‖ ≤ C := by
    rw [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ]
    apply (expandingFreeStep_norm_bound a b k (expandingRadius L τ) (t - τ) ha hk
      (hL.trans (expandingRadius_ge L τ hL hτ.1)) (sub_nonneg.mpr hτ.2) (r τ)).trans
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by
      nlinarith [hτ.2]))).trans (hbound τ hτ)
  have hb := norm_integral_le_of_norm_le (f := expandingDuhamelIntegrand a b k L ha hk hL t r)
    (μ := volume.restrict (Icc 0 t)) (g := fun _ => C)
    (integrableOn_const isCompact_Icc.measure_ne_top)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ; exact hpoint τ hτ)
  simpa only [expandingDuhamel, setIntegral_const, Real.volume_real_Icc_of_le ht, sub_zero,
    smul_eq_mul] using hb

end DefocusingNLS

end OAI
