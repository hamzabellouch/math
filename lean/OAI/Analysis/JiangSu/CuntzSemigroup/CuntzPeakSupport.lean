import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.Ranks

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma mul_sqrt_eq_zero_of_mul_eq_zero {b c : A} (hb : 0≤b) (h : c*b=0) :
    c*CFC.sqrt b=0 := by
  apply (CStarRing.mul_star_self_eq_zero_iff _).mp
  rw [star_mul,(CFC.sqrt_nonneg b).isSelfAdjoint.star_eq]
  calc
    (c*CFC.sqrt b)*(CFC.sqrt b*star c) = (c*(CFC.sqrt b*CFC.sqrt b))*star c := by
      simp only [mul_assoc]
    _=0 := by rw [CFC.sqrt_mul_sqrt_self b hb,h,zero_mul]

lemma peak_multiplier (f : A) (hf : 0≤f) (hfn : ‖f‖≤1)
    (δ : ℝ) (hδ : 0≤δ) :
    ∃ h : A, ‖h‖≤δ ∧ (f-1)*CFC.sqrt (directPositiveCut (1-δ) f) =
      h*CFC.sqrt (directPositiveCut (1-δ) f) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have := hA
    exact ⟨0,by simpa using hδ,Subsingleton.elim _ _⟩
  have := hA
  let g : ℝ → ℝ := fun t => max (t-1) (-δ)
  have hg : Continuous g := (continuous_id.sub continuous_const).max continuous_const
  let h := cfc g f
  have hhn : ‖h‖≤δ := by
    apply norm_cfc_le hδ
    intro t ht
    have ht1 : t≤1 := ((le_abs_self t).trans (spectrum.norm_le_norm_of_mem ht)).trans hfn
    change |max (t-1) (-δ)|≤δ
    rw [abs_le]
    constructor
    · exact le_max_right _ _
    · exact max_le ((sub_nonpos.mpr ht1).trans hδ) ((neg_nonpos.mpr hδ).trans hδ)
  have hprod : (f-1-h)*directPositiveCut (1-δ) f=0 := by
    have he : f-1-h=cfc (fun t : ℝ => t-1-g t) f := by
      rw [cfc_sub _ _ f (by fun_prop) hg.continuousOn,
        cfc_sub _ _ f (by fun_prop) (by fun_prop),
        cfc_id' ℝ f hf.isSelfAdjoint,cfc_const_one ℝ f]
    rw [he]
    change cfc _ f*cfc _ f=0
    rw [←cfc_mul _ _ f (by fun_prop) (by fun_prop),←cfc_zero ℝ f]
    apply cfc_congr
    intro t _
    change (t-1-max (t-1) (-δ))*max (t-(1-δ)) 0=0
    by_cases ht : t≤1-δ
    · rw [max_eq_right (sub_nonpos.mpr ht), mul_zero]
    · rw [max_eq_left (by linarith),sub_self,zero_mul]
  have hz := mul_sqrt_eq_zero_of_mul_eq_zero (directPositiveCut_nonneg (1-δ) f) hprod
  rw [sub_mul,sub_eq_zero] at hz
  exact ⟨h,hhn,hz⟩

theorem approximate_peak_isometry (a f : A) (han : ‖a‖≤1) (hf : 0≤f) (hfn : ‖f‖≤1)
    (δ : ℝ) (hδ : 0≤δ) (hcmp : CuntzSubequiv a (directPositiveCut (1-δ) f))
    (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    ∃ s : A, ‖s‖≤2 ∧ ‖star s*s-a‖<ε ∧ ‖f*s-s‖≤2*δ := by
  let b := directPositiveCut (1-δ) f
  have hbp : 0≤b := directPositiveCut_nonneg _ _
  obtain ⟨v,hv⟩ := (cuntzSubequiv_iff_norm _ _).mp hcmp ε hε
  let s := CFC.sqrt b*v
  have he : star s*s=star v*b*v := by
    simp only [s,star_mul,(CFC.sqrt_nonneg b).isSelfAdjoint.star_eq]
    calc
      star v*CFC.sqrt b*(CFC.sqrt b*v) = star v*(CFC.sqrt b*CFC.sqrt b)*v := by
        simp only [mul_assoc]
      _=star v*b*v := by rw [CFC.sqrt_mul_sqrt_self b hbp]
  have hs : ‖star s*s-a‖<ε := by simpa only [he,norm_sub_rev] using hv
  have hsq : ‖s‖*‖s‖≤2 := by
    rw [←CStarRing.norm_star_mul_self]
    have hn : ‖star s*s‖≤‖star s*s-a‖+‖a‖ := norm_le_norm_sub_add _ _
    linarith
  have hsn : ‖s‖≤2 := by nlinarith [norm_nonneg s]
  obtain ⟨h,hhn,hh⟩ := peak_multiplier f hf hfn δ hδ
  have hfs : f*s-s=h*s := by
    have hsub : f*s-s=(f-1)*s := by rw [sub_mul,one_mul]
    rw [hsub]
    change (f-1)*(CFC.sqrt b*v)=h*(CFC.sqrt b*v)
    rw [←mul_assoc,hh,mul_assoc]
  refine ⟨s,hsn,hs,?_⟩
  rw [hfs]
  exact (norm_mul_le _ _).trans ((mul_le_mul hhn hsn (norm_nonneg _) hδ).trans_eq (mul_comm _ _))

end DirectComparison

end
end

end OAI
