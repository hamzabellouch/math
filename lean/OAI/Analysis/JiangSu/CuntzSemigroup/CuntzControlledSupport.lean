import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzPeakSupport

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma controlled_cut_inverse (w : A) (hw : 0 ≤ w) {β : ℝ} (hβ : 0<β) :
    ∃ k : A, ‖k‖ ≤ β⁻¹ ∧
      w*k*CFC.sqrt (directPositiveCut β w)=CFC.sqrt (directPositiveCut β w) := by
  let q : ℝ → ℝ := fun t => (max β t)⁻¹
  have hq : Continuous q := by
    apply Continuous.inv₀ (by fun_prop)
    intro t
    exact (hβ.trans_le (le_max_left _ _)).ne'
  let k := cfc q w
  have hk : ‖k‖ ≤ β⁻¹ := by
    apply norm_cfc_le (inv_nonneg.mpr hβ.le)
    intro t _
    change |(max β t)⁻¹| ≤ β⁻¹
    rw [abs_of_nonneg (inv_nonneg.mpr (hβ.le.trans (le_max_left _ _)))]
    exact inv_anti₀ hβ (le_max_left _ _)
  have hz : (w*k-1)*directPositiveCut β w=0 := by
    have he : w*k-1=cfc (fun t : ℝ => t*q t-1) w := by
      rw [cfc_sub (fun t : ℝ => t*q t) (fun _ : ℝ => 1) w (continuous_id.mul hq).continuousOn continuousOn_const,
        cfc_mul (fun t : ℝ => t) q w continuousOn_id hq.continuousOn,cfc_id' ℝ w hw.isSelfAdjoint,
        cfc_const_one ℝ w]
    rw [he]
    change cfc _ w*cfc _ w=0
    rw [←cfc_mul _ _ w (by fun_prop) (by fun_prop),←cfc_zero ℝ w]
    apply cfc_congr
    intro t _
    change (t*(max β t)⁻¹-1)*max (t-β) 0=0
    by_cases ht : t ≤ β
    · rw [max_eq_right (sub_nonpos.mpr ht),mul_zero]
    · have cutoff_pos : 0 < t := hβ.trans (lt_of_not_ge ht)
      rw [max_eq_right (le_of_not_ge ht), mul_inv_cancel₀ cutoff_pos.ne', sub_self,
        zero_mul]
  have hzs := mul_sqrt_eq_zero_of_mul_eq_zero (directPositiveCut_nonneg β w) hz
  rw [sub_mul,one_mul,sub_eq_zero] at hzs
  exact ⟨k,hk,hzs⟩

theorem approximate_controlled_isometry (a w h f : A) (han : ‖a‖ ≤ 1) (hw : 0 ≤ w)
    (hhw : h*w=w) {β ε : ℝ} (hβ : 0<β) (hε : 0<ε) (hε1 : ε ≤ 1)
    (hcmp : CuntzSubequiv a (directPositiveCut β w)) :
    ∃ s : A, ‖s‖ ≤ 2 ∧ ‖star s*s-a‖<ε ∧ h*s=s ∧
      ‖f*s-s‖ ≤ 2*β⁻¹*‖f*w-w‖ := by
  let b := directPositiveCut β w
  obtain ⟨v,hv⟩ := (cuntzSubequiv_iff_norm _ _).mp hcmp ε hε
  let s := CFC.sqrt b*v
  have he : star s*s=star v*b*v := by
    simp only [s,star_mul,(CFC.sqrt_nonneg b).isSelfAdjoint.star_eq]
    calc
      star v*CFC.sqrt b*(CFC.sqrt b*v)=star v*(CFC.sqrt b*CFC.sqrt b)*v := by
        simp only [mul_assoc]
      _=star v*b*v := by rw [CFC.sqrt_mul_sqrt_self b (directPositiveCut_nonneg β w)]
  have herr : ‖star s*s-a‖<ε := by simpa only [he,norm_sub_rev] using hv
  have hsn : ‖s‖ ≤ 2 := by
    have ht := norm_le_norm_sub_add (star s*s) a
    rw [CStarRing.norm_star_mul_self] at ht
    nlinarith [norm_nonneg s]
  obtain ⟨k,hkn,hks⟩ := controlled_cut_inverse w hw hβ
  have hfix : w*k*s=s := by
    change w*k*(CFC.sqrt b*v)=CFC.sqrt b*v
    rw [←mul_assoc,hks]
  have hsupport : h*s=s := by
    calc
      h*s=h*(w*k*s) := congrArg (h*·) hfix.symm
      _=(h*w)*k*s := by simp only [mul_assoc]
      _=s := by rw [hhw,hfix]
  have hid : f*s-s=(f*w-w)*k*s := by
    calc
      f*s-s=f*(w*k*s)-w*k*s := by rw [hfix]
      _=(f*w-w)*k*s := by noncomm_ring
  refine ⟨s,hsn,herr,hsupport,?_⟩
  rw [hid]
  calc
    ‖(f*w-w)*k*s‖ ≤ (‖f*w-w‖*‖k‖)*‖s‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖f*w-w‖*β⁻¹)*2 := mul_le_mul
      (mul_le_mul_of_nonneg_left hkn (norm_nonneg _)) hsn (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hβ.le))
    _=2*β⁻¹*‖f*w-w‖ := by ring

end DirectComparison

end
end

end OAI
