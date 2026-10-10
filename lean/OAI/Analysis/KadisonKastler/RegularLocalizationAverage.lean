import OAI.Analysis.KadisonKastler.RegularPacketLocalization
import OAI.Analysis.KadisonKastler.RegularCoreDensePeriods

namespace OAI

/-! # Bounded Haar averages of localized operators

The translated-cutoff analysis map takes values in an actual Hilbert
space of square-integrable vectors. Sandwiching a constant amplification
by this map constructs the Haar average without requiring operator-norm
measurability.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)

include hfinite in
private theorem localFrame_memLp (f : RegularCoreHilbert H) :
    MemLp (fun r : ℝ => regularIndicatorProjection s hs (regularTranslateApply r f))
      2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    ((regularIndicatorProjection s hs).continuous.comp
      (continuous_regularTranslateApply f)).aestronglyMeasurable).mpr
  exact integrable_norm_local_translation_sq s hs hfinite f

/-- The continuous analysis map of the translated scalar cutoff. -/
def regularLocalFrameValue (f : RegularCoreHilbert H) :
    Lp (RegularCoreHilbert H) 2 (volume : Measure ℝ) :=
  (localFrame_memLp s hs hfinite f).toLp _

theorem regularLocalFrameValue_apply_ae (f : RegularCoreHilbert H) :
    regularLocalFrameValue s hs hfinite f =ᵐ[volume]
      fun r => regularIndicatorProjection s hs (regularTranslateApply r f) :=
  (localFrame_memLp s hs hfinite f).coeFn_toLp

theorem norm_regularLocalFrameValue_sq (f : RegularCoreHilbert H) :
    ‖regularLocalFrameValue s hs hfinite f‖ ^ 2 =
      (volume s).toReal * ‖f‖ ^ 2 := by
  rw [← regular_integral_norm_sq]
  calc
    (∫ r : ℝ, ‖regularLocalFrameValue s hs hfinite f r‖ ^ 2) =
        ∫ r : ℝ, ‖regularIndicatorProjection s hs (regularTranslateApply r f)‖ ^ 2 := by
      apply integral_congr_ae
      exact (regularLocalFrameValue_apply_ae s hs hfinite f).fun_comp
        (fun x => ‖x‖ ^ 2)
    _ = _ := integral_norm_local_translation_sq s hs hfinite f

theorem norm_regularLocalFrameValue (f : RegularCoreHilbert H) :
    ‖regularLocalFrameValue s hs hfinite f‖ = Real.sqrt (volume s).toReal * ‖f‖ := by
  have hsq := norm_regularLocalFrameValue_sq s hs hfinite f
  have hsqrt : (Real.sqrt (volume s).toReal * ‖f‖) ^ 2 =
      (volume s).toReal * ‖f‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (ENNReal.toReal_nonneg)]
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    (hsq.trans hsqrt.symm)

/-- The translated-cutoff analysis map is bounded with its exact frame constant. -/
def regularLocalFrame : RegularCoreHilbert H →L[ℂ]
    Lp (RegularCoreHilbert H) 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous
    { toFun := regularLocalFrameValue s hs hfinite
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [regularLocalFrameValue_apply_ae s hs hfinite (f + g),
          regularLocalFrameValue_apply_ae s hs hfinite f,
          regularLocalFrameValue_apply_ae s hs hfinite g,
          Lp.coeFn_add (regularLocalFrameValue s hs hfinite f)
            (regularLocalFrameValue s hs hfinite g)] with r hfg hf hg hsum
        rw [hfg, hsum]
        simp only [Pi.add_apply, hf, hg]
        change regularIndicatorProjection s hs
          ((regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
            RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (f + g)) = _
        rw [map_add, map_add]
        rfl
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [regularLocalFrameValue_apply_ae s hs hfinite (c • f),
          regularLocalFrameValue_apply_ae s hs hfinite f,
          Lp.coeFn_smul c (regularLocalFrameValue s hs hfinite f)] with r hcf hf hsmul
        simp only [RingHom.id_apply]
        rw [hcf, hsmul]
        simp only [Pi.smul_apply, hf]
        change regularIndicatorProjection s hs
          ((regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
            RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (c • f)) =
          c • regularIndicatorProjection s hs (regularTranslateApply r f)
        rw [map_smul, map_smul]
        rfl }
    (Real.sqrt (volume s).toReal)
    (fun f => (norm_regularLocalFrameValue s hs hfinite f).le)

theorem norm_regularLocalFrame_le :
    ‖regularLocalFrame (H := H) s hs hfinite‖ ≤ Real.sqrt (volume s).toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  exact (norm_regularLocalFrameValue s hs hfinite f).le

/-- The unnormalized Haar average of localized copies of an operator. -/
def regularLocalizationAverage
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  (regularLocalFrame s hs hfinite).adjoint.comp
    ((T.compLpL 2 (volume : Measure ℝ)).comp (regularLocalFrame s hs hfinite))

private theorem norm_frame_sandwich_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →L[ℂ] F) (A : F →L[ℂ] F) (c d : ℝ)
    (hc : 0 ≤ c) (hV : ‖V‖ ≤ c) (hA : ‖A‖ ≤ d) :
    ‖V.adjoint.comp (A.comp V)‖ ≤ c ^ 2 * d := by
  have hadj : ‖V.adjoint‖ = ‖V‖ := ContinuousLinearMap.adjoint.norm_map V
  calc
    ‖V.adjoint.comp (A.comp V)‖ ≤ ‖V.adjoint‖ * (‖A‖ * ‖V‖) :=
      (V.adjoint.opNorm_comp_le (A.comp V)).trans
        (mul_le_mul_of_nonneg_left (A.opNorm_comp_le V) (norm_nonneg _))
    _ ≤ c * (d * c) := by
      rw [hadj]
      have hd : 0 ≤ d := (norm_nonneg A).trans hA
      exact mul_le_mul hV (mul_le_mul hA hV (norm_nonneg _) hd)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc
    _ = c ^ 2 * d := by ring

theorem norm_regularLocalizationAverage_le
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
    ‖regularLocalizationAverage s hs hfinite T‖ ≤ (volume s).toReal * ‖T‖ := by
  have he := norm_frame_sandwich_le (regularLocalFrame (H := H) s hs hfinite)
    (T.compLpL 2 (volume : Measure ℝ)) (Real.sqrt (volume s).toReal) ‖T‖
    (Real.sqrt_nonneg _) (norm_regularLocalFrame_le s hs hfinite)
    (T.norm_compLpL_le (p := 2) (μ := (volume : Measure ℝ)))
  rw [Real.sq_sqrt (ENNReal.toReal_nonneg)] at he
  exact he

/-- Matrix coefficients of the Haar average are the actual scalar integrals. -/
theorem inner_regularLocalizationAverage
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (f g : RegularCoreHilbert H) :
    inner ℂ f (regularLocalizationAverage s hs hfinite T g) =
      ∫ r : ℝ, inner ℂ (regularIndicatorProjection s hs (regularTranslateApply r f))
        (T (regularIndicatorProjection s hs (regularTranslateApply r g))) := by
  change inner ℂ f ((regularLocalFrame s hs hfinite).adjoint
    (T.compLpL 2 volume (regularLocalFrame s hs hfinite g))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularLocalFrameValue_apply_ae s hs hfinite f,
    regularLocalFrameValue_apply_ae s hs hfinite g,
    T.coeFn_compLpL (p := 2) (μ := (volume : Measure ℝ))
      (regularLocalFrame s hs hfinite g)] with r hf hg hT
  change inner ℂ (regularLocalFrameValue s hs hfinite f r)
    ((T.compLpL 2 volume (regularLocalFrame s hs hfinite g)) r) = _
  rw [hf, hT]
  change inner ℂ (regularIndicatorProjection s hs (regularTranslateApply r f))
    (T (regularLocalFrameValue s hs hfinite g r)) = _
  rw [hg]

end

end KadisonKastler

end OAI
