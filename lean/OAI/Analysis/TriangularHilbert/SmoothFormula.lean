import OAI.Analysis.TriangularHilbert.DiscretePairing

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

def scalePrimitive (s t : ℝ) : ℝ :=
  2*(Real.sqrt s*((t^2/9)/s-1/3))*density (3*s) t/t

lemma density_three_hasDerivAt {s : ℝ} (hs : 0 < s) (t : ℝ) :
    HasDerivAt (fun s => density (3*s) t)
      ((1/2)*((t/(3*s))^2-(3*s)⁻¹)*density (3*s) t*3) s := by
  have hd := (weight_hasDerivAt_variance 1 t 0 (3*s) (by positivity)).comp s
    ((hasDerivAt_id s).const_mul 3)
  simpa only [weight,score,sub_zero,one_mul,mul_one,Function.comp_def] using hd

lemma scalePrimitive_hasDerivAt {s t : ℝ} (hs : 0 < s) (ht : t ≠ 0) :
    HasDerivAt (fun s => scalePrimitive s t) (signedKernel s t/s) s := by
  have hr := Real.hasDerivAt_sqrt hs.ne'
  have hq := ((hasDerivAt_const s (t^2/9)).div (hasDerivAt_id s) hs.ne').sub_const (1/3)
  have hd := ((((hr.mul hq).const_mul 2).mul (density_three_hasDerivAt hs t)).div_const t)
  convert! hd using 1
  unfold signedKernel
  dsimp
  field_simp
  ring_nf
  simp only [Real.sq_sqrt hs.le]
  ring

lemma smoothKernel_eq_primitive {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : t ≠ 0) :
    (∫ s in a..b, signedKernel s t/s) = scalePrimitive b t-scalePrimitive a t := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s hs
    rw [Set.uIcc_of_le hab] at hs
    exact scalePrimitive_hasDerivAt (ha.trans_le hs.1) ht
  · exact signedKernel_intervalIntegrable ha hab t

def kernelConstant : ℝ := -(2/3)*density 3 0

def kernelProfile (v : ℝ) : ℝ := kernelConstant-2*(v^2/9-1/3)*density 3 v

lemma kernelConstant_ne_zero : kernelConstant ≠ 0 := by
  unfold kernelConstant
  exact mul_ne_zero (by norm_num) (density_pos (by norm_num) 0).ne'

lemma scalePrimitive_profile {s t : ℝ} (hs : 0 < s) :
    scalePrimitive s t = (kernelConstant-kernelProfile (t/Real.sqrt s))/t := by
  have hd := density_dilation hs (by norm_num : 0 < (3:ℝ)) t
  have he : density 3 (t/Real.sqrt s) = Real.sqrt s*density (3*s) t := by
    rw [hd]
    field_simp
  unfold kernelProfile scalePrimitive
  rw [he]
  field_simp
  rw [Real.sq_sqrt hs.le]
  ring

lemma smoothKernel_eq_profile {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : t ≠ 0) :
    (∫ s in a..b, signedKernel s t/s) =
      (kernelProfile (t/Real.sqrt a)-kernelProfile (t/Real.sqrt b))/t := by
  rw [smoothKernel_eq_primitive ha hab ht,scalePrimitive_profile (ha.trans_le hab),scalePrimitive_profile ha]
  ring
end
end TriangularHilbert.Heat
end

end OAI
