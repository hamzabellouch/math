import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

noncomputable section
namespace CStarProjectionRounding
open scoped CStarAlgebra

def rounding (t : ℝ) : ℝ := max 0 (min 1 (2*t-1/2))
lemma continuous_rounding : Continuous rounding := by
  unfold rounding
  fun_prop

lemma scalar_rounding {t : ℝ} (h : |t-t*t|≤1/16) :
    (rounding t=0 ∨ rounding t=1) ∧ |rounding t-t|≤1/8 := by
  have hg : t≤1/4 ∨ 3/4≤t := by
    by_contra! hbad
    have hh := mul_pos (sub_pos.mpr hbad.1) (sub_pos.mpr hbad.2)
    have hu := (abs_le.mp h).2
    nlinarith
  rcases hg with ht|ht
  · have hr : rounding t=0 := by
      unfold rounding
      rw [min_eq_right (by linarith),max_eq_left (by linarith)]
    refine ⟨Or.inl hr,?_⟩
    rw [hr,zero_sub,abs_neg]
    have ha : 1/2≤|1-t| := (by linarith : (1/2:ℝ)≤1-t).trans (le_abs_self _)
    have hm := mul_le_mul_of_nonneg_left ha (abs_nonneg t)
    have hid : |t| * |1-t|=|t-t*t| := by
      rw [← abs_mul, mul_sub, mul_one]
    rw [hid] at hm
    linarith
  · have hr : rounding t=1 := by
      unfold rounding
      rw [min_eq_left (by linarith),max_eq_right (by norm_num)]
    refine ⟨Or.inr hr,?_⟩
    rw [hr]
    have ha : 1/2≤|t| := (by linarith : (1/2:ℝ)≤t).trans (le_abs_self _)
    have hm := mul_le_mul_of_nonneg_right ha (abs_nonneg (1-t))
    have hid : |t| * |1-t|=|t-t*t| := by
      rw [← abs_mul, mul_sub, mul_one]
    rw [hid] at hm
    linarith

variable {A : Type*} [CStarAlgebra A]

lemma exists_nearby_projection {a : A} (ha : IsSelfAdjoint a) (hd : ‖a-a*a‖≤1/16) :
    ∃ q : A, IsStarProjection q ∧ ‖q-a‖≤1/8 := by
  have hc := continuous_rounding.continuousOn (s := spectrum ℝ a)
  have hspec : ∀ t ∈ spectrum ℝ a, |t-t*t|≤1/16 := by
    intro t ht
    have h := norm_apply_le_norm_cfc (fun x : ℝ => x-x*x) a ht
    rw [cfc_sub (fun x : ℝ => x) (fun x => x*x) a,
      cfc_mul (fun x : ℝ => x) (fun x => x) a,cfc_id' ℝ a ha] at h
    exact h.trans hd
  refine ⟨cfc rounding a,?_,?_⟩
  · constructor
    · change cfc rounding a * cfc rounding a = cfc rounding a
      rw [←cfc_mul rounding rounding a hc hc]
      apply cfc_congr
      intro t ht
      rcases (scalar_rounding (hspec t ht)).1 with h|h <;> simp [h]
    · exact cfc_predicate rounding a
  · have he : cfc rounding a-a=cfc (fun t => rounding t-t) a := by
      rw [cfc_sub rounding (fun t : ℝ => t) a hc (by fun_prop),cfc_id' ℝ a ha]
    rw [he]
    apply norm_cfc_le (by norm_num)
    intro t ht
    exact (scalar_rounding (hspec t ht)).2

lemma idempotent_of_norm_lt_one {x : A} (hx : IsIdempotentElem x) (hn : ‖x‖<1) : x=0 := by
  apply norm_eq_zero.mp
  have he : ‖x‖≤‖x‖*‖x‖ := by
    calc ‖x‖=‖x*x‖ := congrArg norm hx.symm
         _≤‖x‖*‖x‖ := norm_mul_le x x
  have hnon := norm_nonneg x
  nlinarith

end CStarProjectionRounding

end
end

end OAI
