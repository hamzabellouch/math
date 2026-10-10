import Mathlib
import OAI.Geometry.PrescribedRicci.GlobalKahlerIntegral

namespace OAI

/-! Lp Power Bounds. -/

section

 

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace TameInterpolation
variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

lemma lpNorm_mul_le {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {f g : Y → ℝ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    lpNorm (fun x => f x*g x) r μ ≤ lpNorm f p μ*lpNorm g q μ := by
  have he := eLpNorm_smul_le_mul_eLpNorm (p:=p) (q:=q) (r:=r)
    hf.aestronglyMeasurable hg.aestronglyMeasurable
  change eLpNorm (fun x => f x*g x) r μ ≤ eLpNorm f p μ * eLpNorm g q μ at he
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) he
  simpa only [ENNReal.toReal_mul,toReal_eLpNorm] using hh

lemma lpNorm_norm_rpow {E : Type*} [NormedAddCommGroup E]
    (f : Y → E) (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) {q : ℝ} (hq : 0 < q) :
    lpNorm (fun x => ‖f x‖^q) p μ = (lpNorm f (p*ENNReal.ofReal q) μ)^q := by
  rw [← toReal_eLpNorm,eLpNorm_norm_rpow f hf hq,
    ← ENNReal.toReal_rpow,toReal_eLpNorm]

lemma lpNorm_rpow_integral {E : Type*} [NormedAddCommGroup E]
    (f : Y → E) (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    (lpNorm f (ENNReal.ofReal p) μ)^p = ∫ x, ‖f x‖^p ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le]
  rw [← Real.rpow_mul (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)]
  simp [hp.ne']

lemma integral_norm_le_lpNorm {f : Y → ℝ} (hf : AEStronglyMeasurable f μ) :
    |∫ x, f x ∂μ| ≤ lpNorm f 1 μ := by
  rw [lpNorm_one_eq_integral_norm hf]
  exact norm_integral_le_integral_norm f

end TameInterpolation

end
end

end OAI
