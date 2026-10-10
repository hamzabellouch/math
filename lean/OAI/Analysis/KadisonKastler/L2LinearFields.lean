import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

namespace OAI

/-! # Lifting fields of maps between different Hilbert spaces to L²

This supplies the varying synthesis maps used on a fixed dimension stratum.
Measurability is required only after evaluation on a vector.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (μ : Measure X)

theorem aestronglyMeasurable_linearField_apply (T : X → E →L[ℂ] F)
    (hT : ∀ v, AEStronglyMeasurable (fun x => T x v) μ)
    (v : X → E) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x => T x (v x)) μ := by
  have haux (w : X → E) (hw : StronglyMeasurable w) :
      AEStronglyMeasurable (fun x => T x (w x)) μ := by
    induction w, hw using StronglyMeasurable.induction with
    | @ind v s hs =>
      convert (hT v).indicator hs using 1
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    | add hf hg hfg hdisj ihf ihg =>
      convert ihf.add ihg using 1
      funext x
      simp only [Pi.add_apply, map_add]
    | lim hf hg ih hlim =>
      exact aestronglyMeasurable_of_tendsto_ae atTop ih
        (Eventually.of_forall fun x => (T x).continuous.tendsto _ |>.comp (hlim x))
  exact (haux (hv.mk v) hv.stronglyMeasurable_mk).congr
    (hv.ae_eq_mk.symm.mono fun x hx => congrArg (T x) hx)

theorem l2LinearFieldMemLp (T : X → E →L[ℂ] F)
    (hT : ∀ v, AEStronglyMeasurable (fun x => T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (f : Lp E 2 μ) :
    MemLp (fun x => T x (f x)) 2 μ := by
  apply ((Lp.memLp f).norm.const_mul C).mono'
    (aestronglyMeasurable_linearField_apply μ T hT f (Lp.aestronglyMeasurable f))
  filter_upwards [hC] with x hx
  exact ((T x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

def l2LinearFieldApply (T : X → E →L[ℂ] F)
    (hT : ∀ v, AEStronglyMeasurable (fun x => T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (f : Lp E 2 μ) : Lp F 2 μ :=
  (l2LinearFieldMemLp μ T hT C hC f).toLp _

theorem l2LinearFieldApply_ae (T : X → E →L[ℂ] F)
    (hT : ∀ v, AEStronglyMeasurable (fun x => T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (f : Lp E 2 μ) :
    l2LinearFieldApply μ T hT C hC f =ᵐ[μ] fun x => T x (f x) :=
  MemLp.coeFn_toLp _

def l2LinearFieldMap (T : X → E →L[ℂ] F)
    (hT : ∀ v, AEStronglyMeasurable (fun x => T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) : Lp E 2 μ →L[ℂ] Lp F 2 μ :=
  LinearMap.mkContinuous
    { toFun := l2LinearFieldApply μ T hT C hC
      map_add' f g := by
        apply Lp.ext
        filter_upwards [l2LinearFieldApply_ae μ T hT C hC (f + g),
          l2LinearFieldApply_ae μ T hT C hC f, l2LinearFieldApply_ae μ T hT C hC g,
          Lp.coeFn_add f g,
          Lp.coeFn_add (l2LinearFieldApply μ T hT C hC f)
            (l2LinearFieldApply μ T hT C hC g)] with x hfg hf hg ha hb
        rw [hfg, hb, ha]
        simp only [Pi.add_apply]
        rw [hf, hg, map_add]
      map_smul' c f := by
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [l2LinearFieldApply_ae μ T hT C hC (c • f),
          l2LinearFieldApply_ae μ T hT C hC f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (l2LinearFieldApply μ T hT C hC f)] with x hc hf ha hb
        rw [hc, hb, ha]
        simp only [Pi.smul_apply]
        rw [hf, map_smul] }
    C (by
      intro f
      change ‖l2LinearFieldApply μ T hT C hC f‖ ≤ C * ‖f‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [l2LinearFieldApply_ae μ T hT C hC f, hC] with x hx hn
      rw [hx]
      exact ((T x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _)))

theorem isometryField_norm_bound (U : X → E →ₗᵢ[ℂ] F) :
    ∀ᵐ x ∂μ, ‖(U x).toContinuousLinearMap‖ ≤ 1 :=
  Eventually.of_forall fun x => (U x).norm_toContinuousLinearMap_le

/-- Pointwise isometries give a genuine isometric inclusion of L² spaces. -/
def l2IsometryField (U : X → E →ₗᵢ[ℂ] F)
    (hU : ∀ v, AEStronglyMeasurable (fun x => U x v) μ) :
    Lp E 2 μ →ₗᵢ[ℂ] Lp F 2 μ where
  toLinearMap := (l2LinearFieldMap μ (fun x => (U x).toContinuousLinearMap) hU 1
    (isometryField_norm_bound μ U)).toLinearMap
  norm_map' f := by
    change ‖l2LinearFieldApply μ (fun x => (U x).toContinuousLinearMap) hU 1
      (isometryField_norm_bound μ U) f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def,
      eLpNorm_congr_ae (l2LinearFieldApply_ae μ _ hU 1 (isometryField_norm_bound μ U) f)]
    congr 1
    apply eLpNorm_congr_norm_ae
      (aestronglyMeasurable_linearField_apply μ _ hU f (Lp.aestronglyMeasurable f))
      (Lp.aestronglyMeasurable f)
    exact Eventually.of_forall fun x => (U x).norm_map (f x)

theorem l2IsometryField_ae (U : X → E →ₗᵢ[ℂ] F)
    (hU : ∀ v, AEStronglyMeasurable (fun x => U x v) μ) (f : Lp E 2 μ) :
    l2IsometryField μ U hU f =ᵐ[μ] fun x => U x (f x) :=
  l2LinearFieldApply_ae μ _ hU 1 (isometryField_norm_bound μ U) f

end

end KadisonKastler

end OAI
