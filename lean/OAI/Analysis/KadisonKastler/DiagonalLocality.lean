import OAI.Analysis.KadisonKastler.FrequencyNest
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

namespace OAI

/-! # Pointwise locality of operators commuting with scalar multipliers

Cutting down the operator norm inequality by every measurable indicator
gives the same inequality pointwise. This is the boundedness step in
constructing the diagonal field, before choosing any representatives.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
theorem regular_integral_norm_sq (f : RegularCoreHilbert H) :
    (∫ t : ℝ, ‖f t‖ ^ 2) = ‖f‖ ^ 2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def (𝕜 := ℂ) f f)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)] at h
  simpa only [inner_self_eq_norm_sq] using h.symm

omit [CompleteSpace H] in
theorem regular_setIntegral_norm_sq (s : Set ℝ) (hs : MeasurableSet s)
    (f : RegularCoreHilbert H) :
    (∫ t in s, ‖f t‖ ^ 2) = ‖regularIndicatorProjection s hs f‖ ^ 2 := by
  rw [← regular_integral_norm_sq]
  calc
    (∫ t in s, ‖f t‖ ^ 2) = ∫ t : ℝ, s.indicator (fun t => ‖f t‖ ^ 2) t :=
      (integral_indicator hs).symm
    _ = ∫ t : ℝ, ‖regularIndicatorProjection s hs f t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [regularIndicatorProjection_apply_ae s hs f] with t ht
      rw [ht]
      by_cases hts : t ∈ s <;> simp [hts]

/-- Commuting with all scalar projections makes the ambient operator
norm a pointwise bound on every vector-valued function. -/
theorem ae_norm_apply_le_of_commute_indicators
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ (s : Set ℝ) (hs : MeasurableSet s),
      Commute T (regularIndicatorProjection s hs)) (f : RegularCoreHilbert H) :
    ∀ᵐ t : ℝ, ‖T f t‖ ≤ ‖T‖ * ‖f t‖ := by
  have hsq : (fun t : ℝ => ‖T f t‖ ^ 2) ≤ᵐ[volume]
      (fun t => ‖T‖ ^ 2 * ‖f t‖ ^ 2) := by
    apply ae_le_of_forall_setIntegral_le
      ((Lp.memLp (T f)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
      (((Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul _)
    intro s hs _
    rw [integral_const_mul, regular_setIntegral_norm_sq s hs,
      regular_setIntegral_norm_sq s hs]
    have heq : regularIndicatorProjection s hs (T f) =
        T (regularIndicatorProjection s hs f) :=
      congrArg (fun S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => S f)
        (hT s hs).eq.symm
    rw [heq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
  filter_upwards [hsq] with t ht
  rw [← mul_pow] at ht
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp ht

omit [CompleteSpace H] in
/-- The published diagonal-commutant hypothesis supplies exactly the
indicator commutation used in the local norm argument. -/
theorem commute_indicators_of_commute_scalarMultipliers
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ)
      (hC : ∀ t, ‖φ t‖ ≤ C), Commute T (regularScalarMultiplier φ hφ C hC))
    (s : Set ℝ) (hs : MeasurableSet s) :
    Commute T (regularIndicatorProjection s hs) :=
  hT _ _ _ _

/-- Equal local vector values have equal local images. The exceptional
set may depend on the two vectors, which suffices for a countable core. -/
theorem ae_apply_eq_of_eq_of_commute_indicators
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ (s : Set ℝ) (hs : MeasurableSet s),
      Commute T (regularIndicatorProjection s hs)) (f g : RegularCoreHilbert H) :
    ∀ᵐ t : ℝ, f t = g t → T f t = T g t := by
  have hb := ae_norm_apply_le_of_commute_indicators T hT (f - g)
  rw [map_sub] at hb
  filter_upwards [hb, Lp.coeFn_sub f g, Lp.coeFn_sub (T f) (T g)]
    with t ht hfg hTfg
  intro heq
  rw [hfg, hTfg] at ht
  simp only [Pi.sub_apply, heq, sub_self, norm_zero, mul_zero] at ht
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm ht (norm_nonneg _)))

theorem ae_norm_apply_sub_le_of_commute_indicators
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ (s : Set ℝ) (hs : MeasurableSet s),
      Commute T (regularIndicatorProjection s hs)) (f g : RegularCoreHilbert H) :
    ∀ᵐ t : ℝ, ‖T f t - T g t‖ ≤ ‖T‖ * ‖f t - g t‖ := by
  have hb := ae_norm_apply_le_of_commute_indicators T hT (f - g)
  rw [map_sub] at hb
  filter_upwards [hb, Lp.coeFn_sub f g, Lp.coeFn_sub (T f) (T g)]
    with t ht hfg hTfg
  simpa only [hfg, hTfg, Pi.sub_apply] using ht

end

end KadisonKastler

end OAI
