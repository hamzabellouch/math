import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace OAI

/-! The elementary disk fractional transformations used to improve an
omitted-value extremal embedding. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

def diskFractionalMap (b z : ℂ) : ℂ := (z-b)/(1-star b*z)

lemma diskFractionalMap_denom_ne_zero {b z : ℂ} (hb : ‖b‖<1) (hz : ‖z‖<1) :
    1-star b*z ≠ 0 := by
  intro h
  have he : star b*z=1 := (sub_eq_zero.mp h).symm
  have hn : ‖star b*z‖<1 := by
    rw [norm_mul,norm_star]
    nlinarith [norm_nonneg b,norm_nonneg z]
  rw [he,norm_one] at hn
  exact (lt_irrefl _ hn)

lemma diskFractionalMap_norm_identity (b z : ℂ) :
    ‖1-star b*z‖^2-‖z-b‖^2=(1-‖b‖^2)*(1-‖z‖^2) := by
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.one_re,Complex.one_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma diskFractionalMap_mem_ball {b z : ℂ} (hb : ‖b‖<1) (hz : ‖z‖<1) :
    ‖diskFractionalMap b z‖<1 := by
  have hd := diskFractionalMap_denom_ne_zero hb hz
  have hb' : 0<1-‖b‖^2 := by nlinarith [norm_nonneg b]
  have hz' : 0<1-‖z‖^2 := by nlinarith [norm_nonneg z]
  have he := diskFractionalMap_norm_identity b z
  have hn : ‖z-b‖<‖1-star b*z‖ := by
    nlinarith [mul_pos hb' hz', norm_nonneg (z-b),norm_nonneg (1-star b*z)]
  simpa only [diskFractionalMap,norm_div,div_lt_one (norm_pos_iff.mpr hd)] using hn

lemma diskFractionalMap_hasDerivAt {b z : ℂ} (hb : ‖b‖<1) (hz : ‖z‖<1) :
    HasDerivAt (diskFractionalMap b)
      ((1-star b*b)/(1-star b*z)^2) z := by
  have hd := diskFractionalMap_denom_ne_zero hb hz
  have h := ((hasDerivAt_id z).sub_const b).div
    ((hasDerivAt_const z 1).sub ((hasDerivAt_id z).const_mul (star b))) hd
  convert h using 1
  · rfl
  · dsimp
    ring

lemma diskFractionalMap_injective {b : ℂ} (hb : ‖b‖<1) :
    InjOn (diskFractionalMap b) (ball 0 1) := by
  intro x hx y hy he
  have hx' := diskFractionalMap_denom_ne_zero hb (mem_ball_zero_iff.mp hx)
  have hy' := diskFractionalMap_denom_ne_zero hb (mem_ball_zero_iff.mp hy)
  have hb' := diskFractionalMap_denom_ne_zero hb hb
  have he' := (div_eq_div_iff hx' hy').mp he
  have hf : (x-y)*(1-star b*b)=0 := by
    calc
      (x-y)*(1-star b*b) = (x-b)*(1-star b*y)-(y-b)*(1-star b*x) := by ring
      _ = 0 := sub_eq_zero.mpr he'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hb')

@[simp] lemma diskFractionalMap_self {b : ℂ} : diskFractionalMap b b=0 := by
  simp [diskFractionalMap]

@[simp] lemma diskFractionalMap_zero {b : ℂ} : diskFractionalMap b 0 = -b := by
  simp [diskFractionalMap]

end CircleDomainRigidity

end

end OAI
