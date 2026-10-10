import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! A weighted scalar Cauchy--Schwarz bound used for vertical convolution. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem weighted_integral_cauchySchwarz {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (w g : X → ℝ) (hwm : Measurable w) (hgm : Measurable g)
    (hw : ∀ x, 0≤w x) (hg : ∀ x, 0≤g x)
    (hwi : Integrable w mu) (henergy : Integrable (fun x => w x*g x^2) mu) :
    Integrable (fun x => w x*g x) mu ∧
      (∫ x, w x*g x ∂mu)^2≤(∫ x, w x ∂mu)*(∫ x, w x*g x^2 ∂mu) := by
  let a := fun x => Real.sqrt (w x)
  let b := fun x => Real.sqrt (w x)*g x
  have ha_sq (x) : a x^2=w x := Real.sq_sqrt (hw x)
  have hb_sq (x) : b x^2=w x*g x^2 := by
    dsimp [b]
    rw [mul_pow,Real.sq_sqrt (hw x)]
  have ha : MemLp a 2 mu := (memLp_two_iff_integrable_sq (f:=a)
    (hwm.sqrt.aestronglyMeasurable)).2 (by simpa only [ha_sq] using hwi)
  have hb : MemLp b 2 mu := (memLp_two_iff_integrable_sq (f:=b)
    ((hwm.sqrt.mul hgm).aestronglyMeasurable)).2 (by simpa only [hb_sq] using henergy)
  have heq (x) : a x*b x=w x*g x := by
    dsimp [a,b]
    rw [←mul_assoc,Real.mul_self_sqrt (hw x)]
  have hi : Integrable (fun x => w x*g x) mu := by
    have hi0 := ha.integrable_mul hb
    change Integrable (fun x => a x*b x) mu at hi0
    simpa only [heq] using hi0
  refine ⟨hi,?_⟩
  have hcs : (∫ x, w x*g x ∂mu)≤
      Real.sqrt (∫ x, w x ∂mu)*Real.sqrt (∫ x, w x*g x^2 ∂mu) := by
    simpa only [heq,Real.rpow_two,ha_sq,hb_sq,←Real.sqrt_eq_rpow] using
      integral_mul_le_Lp_mul_Lq_of_nonneg (f:=a) (g:=b) Real.HolderConjugate.two_two
        (Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg (w x)))
        (Filter.Eventually.of_forall (fun x => mul_nonneg (Real.sqrt_nonneg (w x)) (hg x)))
        (by simpa using ha) (by simpa using hb)
  have hs := pow_le_pow_left₀ (integral_nonneg fun x => mul_nonneg (hw x) (hg x)) hcs 2
  rwa [mul_pow,Real.sq_sqrt (integral_nonneg hw),
    Real.sq_sqrt (integral_nonneg fun x => mul_nonneg (hw x) (sq_nonneg (g x)))] at hs

end LipschitzHilbert

end

end OAI
