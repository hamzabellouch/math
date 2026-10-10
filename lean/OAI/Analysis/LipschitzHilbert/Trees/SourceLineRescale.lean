import OAI.Analysis.LipschitzHilbert.Estimates.HorizontalDilation
import OAI.Analysis.LipschitzHilbert.Trees.FiniteLineGrid

namespace OAI

/-! Exact local measure scaling from normalized reference lines to
physical intervals. Relative exceptional-set measure has no scale loss. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

/-- The Jacobian cancels exactly against the interval length. -/
theorem source_line_rescale_measure (r u H : ℝ) (hr : 0 < r)
    (bad : Set ℝ) (hbad : MeasurableSet bad) :
    (volume.restrict (Ico (r*u) (r*(u+H)))) bad =
      ENNReal.ofReal r*(volume.restrict (Ico u (u+H)))
        ((fun x : ℝ => r*x) ⁻¹' bad) := by
  let s := Ico u (u+H) ∩ ((fun x : ℝ => r*x) ⁻¹' bad)
  have hs : MeasurableSet s := measurableSet_Ico.inter (hbad.preimage (by fun_prop))
  have hmap : Measure.map (fun x : ℝ => x/r) volume = ENNReal.ofReal r • volume := by
    simpa only [smul_eq_mul,Module.finrank_self,pow_one,inv_inv,
      abs_of_pos hr,div_eq_mul_inv,mul_comm] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (inv_ne_zero hr.ne'))
  have hpre : (fun x : ℝ => x/r) ⁻¹' s = Ico (r*u) (r*(u+H)) ∩ bad := by
    ext x
    simp only [s,mem_preimage,mem_inter_iff,mem_Ico]
    rw [le_div_iff₀ hr,div_lt_iff₀ hr]
    have heq : r*(x/r) = x := by field_simp
    rw [heq]
    constructor <;> intro h <;> simpa only [mul_comm] using h
  have heq := congrArg (fun μ : Measure ℝ => μ s) hmap
  rw [Measure.map_apply (by fun_prop) hs,hpre] at heq
  rw [Measure.restrict_apply hbad,Measure.restrict_apply (hbad.preimage (by fun_prop))]
  simpa only [Measure.smul_apply,smul_eq_mul,inter_comm] using heq

/-- A normalized relative measure bound holds on its physical interval
with exactly the same relative constant. -/
theorem source_line_rescale_tail (r u H δ : ℝ) (hr : 0 < r) (bad : Set ℝ) (hbad : MeasurableSet bad)
    (hsmall : (volume.restrict (Ico u (u+H))) ((fun x : ℝ => r*x) ⁻¹' bad) ≤
      ENNReal.ofReal δ*ENNReal.ofReal H) :
    (volume.restrict (Ico (r*u) (r*(u+H)))) bad ≤
      ENNReal.ofReal δ*ENNReal.ofReal (r*H) := by
  rw [source_line_rescale_measure r u H hr bad hbad,ENNReal.ofReal_mul hr.le]
  calc
    _ ≤ ENNReal.ofReal r*(ENNReal.ofReal δ*ENNReal.ofReal H) := mul_le_mul' le_rfl hsmall
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
