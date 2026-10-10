import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedBandProjection

namespace OAI

/-! Complex conjugation reflects the Fourier support of an actual
Schwartz function, and preserves its L2 norm and pointwise size. -/
noncomputable section
open MeasureTheory Function
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def schwartzConj (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  f.postcompCLM Complex.conjCLE.toContinuousLinearMap

@[simp] theorem schwartzConj_apply (f : SchwartzMap E ℂ) (x : E) : schwartzConj f x=conj (f x) := rfl

@[simp] theorem schwartzConj_involutive (f : SchwartzMap E ℂ) : schwartzConj (schwartzConj f)=f := by
  ext x
  simp only [schwartzConj_apply,starRingEnd_apply,star_star]

theorem schwartzConj_norm (f : SchwartzMap E ℂ) (x : E) : ‖schwartzConj f x‖=‖f x‖ := by
  simp only [schwartzConj_apply,Complex.norm_conj]

theorem planarFourier_conj (f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (schwartzConj f) omega=conj (planarFourier f (-omega)) := by
  unfold planarFourier
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [schwartzConj_apply,Circle.smul_def,smul_eq_mul,Real.fourierChar_apply,map_mul,
    Prod.fst_neg,Prod.snd_neg,mul_neg,neg_add_rev,neg_neg,←Complex.exp_conj,Complex.conj_ofReal,Complex.conj_I]
  congr 2
  push_cast
  ring

end LipschitzHilbert

end

end OAI
