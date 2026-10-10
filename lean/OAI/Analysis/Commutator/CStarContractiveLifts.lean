import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped CStarAlgebra

namespace Kadison.CStarContractiveLifts

def radial (t : ℝ) : ℝ := (Real.sqrt (max 1 |t|))⁻¹

lemma radial_continuous : Continuous radial := by
  unfold radial
  exact (continuous_const.max continuous_abs).sqrt.inv₀ (fun t =>
    ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|))))

lemma radial_eq_one {t : ℝ} (ht : |t|≤1) : radial t=1 := by
  simp only [radial,max_eq_left ht,Real.sqrt_one,inv_one]

lemma radial_square (t : ℝ) : radial t*radial t=(max 1 |t|)⁻¹ := by
  rw [radial,←mul_inv,←pow_two,Real.sq_sqrt (zero_le_one.trans (le_max_left 1 |t|))]

lemma radial_bound (t : ℝ) : ‖radial t * t * radial t‖≤1 := by
  have hd : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|)
  rw [show radial t*t*radial t=t*(radial t*radial t) by ring,radial_square,
    Real.norm_eq_abs,abs_mul,abs_inv,abs_of_pos hd,←div_eq_mul_inv]
  exact (div_le_one hd).mpr (le_max_right 1 |t|)

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def clip (a : A) : A := a*cfc radial (star a*a)

lemma clip_norm_le (a : A) : ‖clip a‖≤1 := by
  have hs : IsSelfAdjoint (star a*a) := IsSelfAdjoint.star_mul_self a
  have hk : IsSelfAdjoint (cfc radial (star a*a)) := cfc_predicate _ _
  have he : star (clip a)*clip a=cfc (fun t : ℝ => radial t*t*radial t) (star a*a) := by
    rw [clip,star_mul,hk.star_eq]
    calc
      _=cfc radial (star a*a)*(star a*a)*cfc radial (star a*a) := by noncomm_ring
      _=cfc radial (star a*a)*cfc (fun t : ℝ => t) (star a*a)*cfc radial (star a*a) := by
        rw [cfc_id' ℝ _ hs]
      _=_ := by
        rw [←cfc_mul radial (fun t : ℝ => t) _ radial_continuous.continuousOn continuous_id.continuousOn,
          ←cfc_mul (fun t : ℝ => radial t*t) radial _
            (radial_continuous.mul continuous_id).continuousOn radial_continuous.continuousOn]
  have hn : ‖star (clip a)*clip a‖≤1 := by
    rw [he]
    exact norm_cfc_le zero_le_one (fun t _ => radial_bound t)
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (clip a)]

lemma clip_fix {a : A} (ha : ‖a‖≤1) : clip a=a := by
  nontriviality A
  have hn : ‖star a*a‖≤1 := by rw [CStarRing.norm_star_mul_self]; nlinarith [norm_nonneg a]
  have he : cfc radial (star a*a)=1 := by
    rw [cfc_congr (g := fun _ : ℝ => 1) (fun t ht =>
      radial_eq_one ((show |t|≤‖star a*a‖ from spectrum.norm_le_norm_of_mem ht).trans hn)),
      cfc_const_one ℝ _ (IsSelfAdjoint.star_mul_self a)]
  rw [clip,he,mul_one]

lemma map_clip (φ : A →⋆ₐ[ℂ] B) (a : A) : φ (clip a)=clip (φ a) := by
  rw [clip,map_mul,φ.map_cfc radial (star a*a) radial_continuous.continuousOn
    (by fun_prop) (IsSelfAdjoint.star_mul_self a)
    ((IsSelfAdjoint.star_mul_self a).map φ),map_mul,map_star]
  rfl

theorem contraction (φ : A →⋆ₐ[ℂ] B) {b : B} (hb : ‖b‖≤1)
    (hr : b∈Set.range φ) : ∃ a : A, ‖a‖≤1 ∧ φ a=b := by
  obtain ⟨a,rfl⟩ := hr
  exact ⟨clip a,clip_norm_le a,by rw [map_clip,clip_fix hb]⟩

theorem norm_lift (φ : A →⋆ₐ[ℂ] B) {b : B} (hr : b∈Set.range φ) :
    ∃ a : A, ‖a‖≤‖b‖ ∧ φ a=b := by
  by_cases hb : b=0
  · exact ⟨0,by simp [hb],by simp [hb]⟩
  have hn : ‖b‖≠0 := norm_ne_zero_iff.mpr hb
  obtain ⟨y,hy⟩ := hr
  let z : ℂ := (‖b‖⁻¹:ℝ)
  have hz : ‖z • b‖≤1 := by
    rw [norm_smul,show ‖z‖=‖b‖⁻¹ by simp [z],
      inv_mul_cancel₀ hn]
  obtain ⟨x,hx,hex⟩ := contraction φ hz ⟨z • y,by rw [map_smul,hy]⟩
  refine ⟨(‖b‖:ℂ) • x,?_,?_⟩
  · rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg b)]
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg b)).trans_eq (mul_one _)
  · rw [map_smul,hex,smul_smul]
    have he : (‖b‖:ℂ)*z=1 := by
      simp only [z,←Complex.ofReal_mul,mul_inv_cancel₀ hn,Complex.ofReal_one]
    rw [he,one_smul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma operator_norm_lift (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T∈Set.range φ) : ∃ a : A, ‖a‖≤‖T‖ ∧ φ a=T := norm_lift φ hT

end Kadison.CStarContractiveLifts

end

end
end

end OAI
