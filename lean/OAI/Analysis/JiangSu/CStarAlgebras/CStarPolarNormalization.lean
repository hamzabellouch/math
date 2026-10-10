import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

noncomputable section
namespace CStarPolar
open scoped CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

 def cutoffInverseSqrt (t : ℝ) : ℝ := t / (max t (1/2) * Real.sqrt (max t (1/2)))
 lemma cutoff_continuous : Continuous cutoffInverseSqrt := by
  apply continuous_id.div ((continuous_id.max continuous_const).mul
    (Real.continuous_sqrt.comp (continuous_id.max continuous_const)))
  intro t
  apply mul_ne_zero
  · exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (le_max_right _ _))
  · exact ne_of_gt (Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (le_max_right _ _)))
 @[simp] lemma cutoff_zero : cutoffInverseSqrt 0=0 := by simp [cutoffInverseSqrt]
 @[simp] lemma cutoff_one : cutoffInverseSqrt 1=1 := by norm_num [cutoffInverseSqrt]
 lemma cutoff_square (t : ℝ) (ht : 1/2≤t) : cutoffInverseSqrt t*t*cutoffInverseSqrt t=1 := by
  have hp : 0<t := by linarith
  rw [cutoffInverseSqrt,max_eq_left ht]
  have hsq := Real.sq_sqrt hp.le
  have hsn : Real.sqrt t≠0 := ne_of_gt (Real.sqrt_pos.2 hp)
  field_simp
  nlinarith
 lemma cutoff_ne_zero (t : ℝ) (ht : 1/2≤t) : cutoffInverseSqrt t≠0 := by
  have hh := cutoff_square t ht
  intro h
  rw [h,zero_mul,mul_zero] at hh
  exact zero_ne_one hh

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma spectrum_lower [Nontrivial A] {h : A} (hh : ‖h-1‖<1/2)
    {t : ℝ} (ht : t∈spectrum ℝ h) : 1/2≤t := by
  have hm : t-1∈spectrum ℝ (h-1) := by
    rw [←map_one (algebraMap ℝ A),←spectrum.sub_singleton_eq]
    exact Set.sub_mem_sub ht (Set.mem_singleton 1)
  have hb := spectrum.norm_le_norm_of_mem hm
  have hl := neg_abs_le (t-1)
  rw [Real.norm_eq_abs] at hb
  linarith

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma isUnit_of_two_defects {x : A} (hl : ‖star x*x-1‖<1)
    (hr : ‖x*star x-1‖<1) : IsUnit x := by
  have ha : IsUnit (star x*x) := by
    have ht := isUnit_one_sub_of_norm_lt_one (show ‖1-star x*x‖<1 by rwa [norm_sub_rev])
    convert ht using 1; abel
  have hb : IsUnit (x*star x) := by
    have ht := isUnit_one_sub_of_norm_lt_one (show ‖1-x*star x‖<1 by rwa [norm_sub_rev])
    convert ht using 1; abel
  obtain ⟨a,ha₁,ha₂⟩ := isUnit_iff_exists.mp ha
  obtain ⟨b,hb₁,hb₂⟩ := isUnit_iff_exists.mp hb
  apply isUnit_iff_exists_and_exists.mpr
  exact ⟨⟨star x*b,by simpa only [mul_assoc] using hb₁⟩,
    ⟨a*star x,by simpa only [mul_assoc] using ha₂⟩⟩

 def normalize (x : A) : A := x*cfc cutoffInverseSqrt (star x*x)

 omit [PartialOrder A] [StarOrderedRing A] in
 theorem normalize_unitary [Nontrivial A] {x : A}
    (hl : ‖star x*x-1‖<1/2) (hr : ‖x*star x-1‖<1/2) : normalize x∈unitary A := by
  have hsa : IsSelfAdjoint (star x*x) := IsSelfAdjoint.star_mul_self x
  have hs (t : ℝ) (ht : t∈spectrum ℝ (star x*x)) : cutoffInverseSqrt t*t*cutoffInverseSqrt t=1 :=
    cutoff_square t (spectrum_lower hl ht)
  have hg := cfc_predicate cutoffInverseSqrt (star x*x)
  have he : cfc cutoffInverseSqrt (star x*x)*(star x*x)*cfc cutoffInverseSqrt (star x*x)=1 := by
    nth_rw 2 [←cfc_id ℝ (star x*x)]
    rw [←cfc_mul cutoffInverseSqrt id (star x*x) cutoff_continuous.continuousOn (by fun_prop)]
    simp only [id_eq]
    rw [←cfc_mul (fun t => cutoffInverseSqrt t*t) cutoffInverseSqrt (star x*x)
        (cutoff_continuous.mul continuous_id).continuousOn cutoff_continuous.continuousOn]
    rw [cfc_congr hs,cfc_const_one ℝ (star x*x)]
  have hz : star (normalize x)*normalize x=1 := by
    simpa only [normalize,star_mul,hg.star_eq,mul_assoc] using he
  have hu : IsUnit (normalize x) := (isUnit_of_two_defects (hl.trans (by norm_num)) (hr.trans (by norm_num))).mul
    ((isUnit_cfc_iff _ _ cutoff_continuous.continuousOn).mpr (fun t ht => cutoff_ne_zero t (spectrum_lower hl ht)))
  obtain ⟨z,hz₁,hz₂⟩ := isUnit_iff_exists.mp hu
  have hstar : star (normalize x)=z := by
    calc star (normalize x) = star (normalize x)*(normalize x*z) := by rw [hz₁,mul_one]
         _ = z := by rw [←mul_assoc,hz,one_mul]
  exact ⟨hz,by rwa [hstar]⟩

end CStarPolar

end
end

end OAI
