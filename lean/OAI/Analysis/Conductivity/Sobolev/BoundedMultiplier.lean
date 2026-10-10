import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem boundedMultiplier_memLp {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α)
    (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (haC : ∀ᵐ x ∂μ, |a x| ≤ C) (f : Lp E 2 μ) :
    MemLp (fun x => a x • f x) 2 μ :=
  (Lp.memLp f).of_le_mul (ha.smul (Lp.aestronglyMeasurable f)) (by
    filter_upwards [haC] with x hx
    simpa only [norm_smul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (f x)))

def boundedMultiplier {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α)
    (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (_hC : 0 ≤ C) (haC : ∀ᵐ x ∂μ, |a x| ≤ C) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ := by
  let hmem := boundedMultiplier_memLp (E := E) μ a ha C haC
  let T : Lp E 2 μ →ₗ[ℝ] Lp E 2 μ := {
    toFun := fun f => (hmem f).toLp _
    map_add' := by
      intro f g
      apply Lp.ext
      filter_upwards [(hmem (f + g)).coeFn_toLp, (hmem f).coeFn_toLp,
        (hmem g).coeFn_toLp, Lp.coeFn_add f g,
        Lp.coeFn_add ((hmem f).toLp _) ((hmem g).toLp _)] with x hfg hf hg hsum hsum'
      simp only [Pi.add_apply] at hsum hsum'
      rw [hfg, hsum', hf, hg, hsum, smul_add]
    map_smul' := by
      intro c f
      apply Lp.ext
      filter_upwards [(hmem (c • f)).coeFn_toLp, (hmem f).coeFn_toLp,
        Lp.coeFn_smul c f, Lp.coeFn_smul c ((hmem f).toLp _)] with x hcf hf hc hc'
      change ((hmem (c • f)).toLp _) x = (c • ((hmem f).toLp _)) x
      simp only [Pi.smul_apply] at hc hc'
      rw [hcf, hc', hf, hc]
      exact smul_comm _ _ _ }
  exact T.mkContinuous C (fun f => Lp.norm_le_mul_norm_of_ae_le_mul (by
    filter_upwards [(hmem f).coeFn_toLp, haC] with x hx hxC
    change ‖((hmem f).toLp _) x‖ ≤ C * ‖f x‖
    rw [hx, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hxC (norm_nonneg _)))

theorem boundedMultiplier_apply_ae {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α)
    (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ x ∂μ, |a x| ≤ C) (f : Lp E 2 μ) :
    (boundedMultiplier μ a ha C hC haC f : α → E) =ᵐ[μ] fun x => a x • f x := by
  change (((boundedMultiplier_memLp μ a ha C haC f).toLp _) : α → E) =ᵐ[μ] _
  exact MemLp.coeFn_toLp _

def jetGradient : JetFiber →L[ℝ] R3 :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => WithLp.toLp 2 (fun i => z i.succ)
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }

def weakGradientL : H1 →L[ℝ] Lp R3 2 ballMeasure :=
  (jetGradient.compLpL 2 ballMeasure).comp H1Space.subtypeL

theorem weakGradientL_apply_ae (u : H1) :
    (weakGradientL u : R3 → R3) =ᵐ[ballMeasure] weakGradient u :=
  jetGradient.coeFn_compLp u.val

def energyForm (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ x ∂ballMeasure, |a x| ≤ C) :
    H1 →L[ℝ] H1 →L[ℝ] ℝ :=
  ((innerSL ℝ).comp (boundedMultiplier ballMeasure a ha C hC haC |>.comp weakGradientL))
    |>.flip.comp weakGradientL |>.flip

theorem energyForm_apply (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ x ∂ballMeasure, |a x| ≤ C) (u v : H1) :
    energyForm a ha C hC haC u v = energy a u v := by
  change inner ℝ (boundedMultiplier ballMeasure a ha C hC haC (weakGradientL u))
    (weakGradientL v) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMultiplier_apply_ae ballMeasure a ha C hC haC (weakGradientL u),
    weakGradientL_apply_ae u, weakGradientL_apply_ae v] with x hx hu hv
  rw [hx, hu, hv, real_inner_smul_left]

end ScalarConductivity

end

end OAI
