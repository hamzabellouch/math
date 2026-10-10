import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPointFrame
import Mathlib.LinearAlgebra.Matrix.Trace

namespace OAI

/-! Fixed points give a trace bound by transporting to the base point.
These are explicit matrix calculations for the actual hyperbolic action. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaBaseFixed_row_norms (g : SL(2,ℂ))
    (hg : cubicThetaMobius g (0,1)=(0,1)) :
    Complex.normSq (g 0 0)+Complex.normSq (g 0 1)=1 ∧
    Complex.normSq (g 1 0)+Complex.normSq (g 1 1)=1 := by
  have hD : cubicThetaMobiusDenominator g (0,1)=1 := by
    have h := congrArg Prod.snd hg
    change 1/cubicThetaMobiusDenominator g (0,1)=1 at h
    have he := (div_eq_iff (cubicThetaMobius_denominator_pos g (by norm_num)).ne').mp h
    linarith
  have hb : Complex.normSq (g 1 0)+Complex.normSq (g 1 1)=1 := by
    simpa [cubicThetaMobiusDenominator,add_comm] using hD
  have ht := cubicThetaMobius_radius g (p:=(0,1)) (by norm_num)
  rw [hg,hD] at ht
  have ha : Complex.normSq (g 0 0)+Complex.normSq (g 0 1)=1 := by
    simpa [cubicThetaRadius,add_comm] using ht.symm
  exact ⟨ha,hb⟩

lemma cubicThetaBaseFixed_trace_norm (g : SL(2,ℂ))
    (hg : cubicThetaMobius g (0,1)=(0,1)) : ‖g 0 0+g 1 1‖ ≤ 2 := by
  obtain ⟨ha,hd⟩ := cubicThetaBaseFixed_row_norms g hg
  simp only [Complex.normSq_eq_norm_sq] at ha hd
  have ha' : ‖g 0 0‖ ≤ 1 := by nlinarith [sq_nonneg ‖g 0 1‖]
  have hd' : ‖g 1 1‖ ≤ 1 := by nlinarith [sq_nonneg ‖g 1 0‖]
  exact (norm_add_le _ _).trans (by linarith)

lemma cubicThetaBaseFixed_trace_two (g : SL(2,ℂ))
    (hg : cubicThetaMobius g (0,1)=(0,1)) (ht : g 0 0+g 1 1=2) : g=1 := by
  obtain ⟨ha,hd⟩ := cubicThetaBaseFixed_row_norms g hg
  have hr := congrArg Complex.re ht
  have hr2 : (2:ℂ).re=(2:ℝ) := rfl
  rw [Complex.add_re,hr2] at hr
  simp only [Complex.normSq_apply] at ha hd
  have har : (g 0 0).re ≤ 1 := by
    nlinarith [sq_nonneg (g 0 0).im,sq_nonneg (g 0 1).re,sq_nonneg (g 0 1).im]
  have hdr : (g 1 1).re ≤ 1 := by
    nlinarith [sq_nonneg (g 1 1).im,sq_nonneg (g 1 0).re,sq_nonneg (g 1 0).im]
  have har' : (g 0 0).re=1 := by linarith
  have hdr' : (g 1 1).re=1 := by linarith
  rw [har'] at ha
  rw [hdr'] at hd
  have hai : (g 0 0).im=0 := by
    nlinarith [sq_nonneg (g 0 1).re,sq_nonneg (g 0 1).im]
  have hdi : (g 1 1).im=0 := by
    nlinarith [sq_nonneg (g 1 0).re,sq_nonneg (g 1 0).im]
  have hbr : (g 0 1).re=0 := by
    nlinarith [sq_nonneg (g 0 0).im,sq_nonneg (g 0 1).im]
  have hbi : (g 0 1).im=0 := by
    nlinarith [sq_nonneg (g 0 0).im,sq_nonneg (g 0 1).re]
  have hcr : (g 1 0).re=0 := by
    nlinarith [sq_nonneg (g 1 1).im,sq_nonneg (g 1 0).im]
  have hci : (g 1 0).im=0 := by
    nlinarith [sq_nonneg (g 1 1).im,sq_nonneg (g 1 0).re]
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [har',hdr',hai,hdi,hbr,hbi,hcr,hci]

lemma cubicThetaMatrixTrace_conjugate (h g : SL(2,ℂ)) :
    (h⁻¹*g*h) 0 0+(h⁻¹*g*h) 1 1=g 0 0+g 1 1 := by
  have he : Matrix.trace ((h⁻¹*g*h).val)=Matrix.trace g.val := by
    rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.trace_mul_cycle]
    rw [← Matrix.SpecialLinearGroup.coe_mul,mul_inv_cancel,Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mul]
  simpa [Matrix.trace,Fin.sum_univ_two] using he

lemma cubicThetaFixed_trace_norm (p : CubicThetaPoint) (g : SL(2,ℂ))
    (hg : cubicThetaMobius g p.val=p.val) : ‖g 0 0+g 1 1‖ ≤ 2 := by
  have h := cubicThetaBaseFixed_trace_norm _ (cubicThetaPointFrame_conjugate_fixed p g hg)
  rwa [cubicThetaMatrixTrace_conjugate] at h

lemma cubicThetaFixed_trace_two (p : CubicThetaPoint) (g : SL(2,ℂ))
    (hg : cubicThetaMobius g p.val=p.val) (ht : g 0 0+g 1 1=2) : g=1 := by
  have hc : (cubicThetaPointFrame p)⁻¹*g*cubicThetaPointFrame p=1 := by
    apply cubicThetaBaseFixed_trace_two _ (cubicThetaPointFrame_conjugate_fixed p g hg)
    rwa [cubicThetaMatrixTrace_conjugate]
  have he := congrArg (fun u => cubicThetaPointFrame p*u*(cubicThetaPointFrame p)⁻¹) hc
  simpa [mul_assoc] using he

end CubicFirstMoment

end

end OAI
