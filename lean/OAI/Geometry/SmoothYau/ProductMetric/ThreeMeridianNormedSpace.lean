import Mathlib
import OAI.Geometry.SmoothYau.Geometry.ThreeProjectionNormedSpace

namespace OAI

noncomputable section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeMeridianNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeMeridianContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeMeridian_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩

def threeMeridianAmbient (t : ℝ) : Euclidean 3 := Real.cos t • productAxis 1+Real.sin t • productAxis 2
lemma threeMeridianAmbient_norm (t : ℝ) : ‖threeMeridianAmbient t‖=1 := by
  have hn : ‖threeMeridianAmbient t‖^2=1 := by
    rw [←real_inner_self_eq_norm_sq]
    simp only [threeMeridianAmbient,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,productAxis_inner]
    norm_num [Fin.ext_iff]
    nlinarith [Real.sin_sq_add_cos_sq t]
  nlinarith [norm_nonneg (threeMeridianAmbient t)]
def threeMeridian (t : ℝ) : ThreeManifold :=
  (⟨threeMeridianAmbient t,by simpa only [mem_sphere,dist_zero_right] using threeMeridianAmbient_norm t⟩,-1)
lemma threeMeridian_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ThreeModel) ∞ threeMeridian := by
  have h : ContDiff ℝ ∞ threeMeridianAmbient :=
    (Real.contDiff_cos.smul contDiff_const).add (Real.contDiff_sin.smul contDiff_const)
  have hs := h.contMDiff.codRestrict_sphere (n:=2) (fun t => (threeMeridian t).1.property)
  apply contMDiff_reModel_target threeModelEquiv
  rw [modelWithCornersSelf_prod]
  exact hs.prodMk contMDiff_const
lemma threeMeridian_A (t : ℝ) : productA (threeMeridian t).1=((Real.cos t:ℝ):ℂ)*Complex.I := by
  apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,mul_one] <;> simp [productA_re,productA_im,threeMeridian,threeMeridianAmbient,productAxis]
lemma threeMeridian_B (t : ℝ) : productB (threeMeridian t).1=((Real.sin t:ℝ):ℂ)*Complex.I := by
  apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,mul_one] <;> simp [productB_re,productB_im,threeMeridian,threeMeridianAmbient,productAxis]
lemma threeMeridian_circle (t : ℝ) : ((threeMeridian t).2:ℂ)=-1 := by rfl
lemma complex_I_pow_four_add_one (m : ℕ) : Complex.I^(4*m+1)=Complex.I := by
  rw [pow_add,pow_mul]
  norm_num
lemma complex_I_pow_four (m : ℕ) : Complex.I^(4*m)=1 := by rw [pow_mul]; norm_num
lemma complex_neg_one_pow_four_add_one (m : ℕ) : (-1:ℂ)^(4*m+1)=-1 := by
  rw [pow_add,pow_mul]
  norm_num
lemma threeMeridian_complex (r t : ℝ) (m : ℕ) :
    threeCoupledComplex r (4*m+1) (threeMeridian t)=
      -(((Real.cos t)^(4*m+1)+r^(4*m+1)*(Real.sin t)^(4*m+1):ℝ):ℂ)*Complex.I := by
  simp only [threeCoupledComplex,threeMeridian_A,threeMeridian_B,threeMeridian_circle,mul_pow,
    complex_I_pow_four_add_one,complex_neg_one_pow_four_add_one]
  simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow]
  ring
lemma threeMeridian_zero (r t : ℝ) (m : ℕ) : threeCoupled r (4*m+1) (threeMeridian t)=0 := by
  rw [threeCoupled,threeMeridian_complex]
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,neg_zero,sub_zero]
lemma threeMeridian_gradient_value (r t : ℝ) (m : ℕ) :
    coordinateGradientPair threeBackgroundMetric (threeCoupled r (4*m+1))
      (threeCoupled r (4*m+1)) (threeMeridian t)=
      (4*(m:ℝ)+1)^2*(((Real.cos t)^(4*m)+r^(4*m+1)*(Real.sin t)^(4*m))^2+
        ((Real.cos t)^(4*m+1)+r^(4*m+1)*(Real.sin t)^(4*m+1))^2) := by
  rw [threeCoupled_gradient_value r (4*m+1) (by omega),threeMeridian_zero,threeMeridian_complex,
    threeMeridian_A,threeMeridian_B,threeMeridian_circle]
  simp only [Nat.add_sub_cancel,mul_pow,complex_I_pow_four,complex_neg_one_pow_four_add_one]
  simp only [←Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.one_re,Complex.one_im,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
  ring
end YauCounterexamples
end

end OAI
