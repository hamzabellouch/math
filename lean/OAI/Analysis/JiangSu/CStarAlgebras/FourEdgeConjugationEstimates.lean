import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.FourEdgeGroupSurgery
import OAI.Analysis.JiangSu.Absorption.RealUnitaryFlow

namespace OAI

noncomputable section


namespace FourEdgeSurgery
open JiangSuConstruction
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A]


def logarithmicFlow (u : unitary A) : Flow (unitary A) where
  toFun := realUnitaryFlow u
  zero := realUnitaryFlow_zero u
  add := realUnitaryFlow_add u

lemma conjugation_one (a : A) : unitaryConjugation (1 : unitary A) a=a := by
  change (1:A)*a*star (1:A)=a
  simp
lemma conjugation_mul (u v : unitary A) (a : A) :
    unitaryConjugation (u*v) a=unitaryConjugation u (unitaryConjugation v a) := by
  change ((u:A)*(v:A))*a*star ((u:A)*(v:A))=(u:A)*((v:A)*a*star (v:A))*star (u:A)
  simp only [star_mul,mul_assoc]
lemma conjugation_inv_cancel (u : unitary A) (a : A) :
    unitaryConjugation u (unitaryConjugation u⁻¹ a)=a := by
  rw [←conjugation_mul,mul_inv_cancel,conjugation_one]
lemma conjugation_inv_cancel' (u : unitary A) (a : A) :
    unitaryConjugation u⁻¹ (unitaryConjugation u a)=a := by
  rw [←conjugation_mul,inv_mul_cancel,conjugation_one]

lemma conjugation_distance (u : unitary A) (a b : A) :
    ‖unitaryConjugation u a-unitaryConjugation u b‖≤‖a-b‖ := by
  rw [←map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le (unitaryConjugation u) _

lemma conjugation_comp_error (u v : unitary A) (a b c : A) :
    ‖unitaryConjugation (u*v) a-c‖≤
      ‖unitaryConjugation v a-b‖+‖unitaryConjugation u b-c‖ := by
  rw [conjugation_mul]
  exact (norm_sub_le_norm_sub_add_norm_sub _ (unitaryConjugation u b) _).trans
    (add_le_add (conjugation_distance u _ b) le_rfl)

lemma conjugation_change_test (u : unitary A) (a b : A) :
    ‖unitaryConjugation u a-a‖≤2*‖a-b‖+‖unitaryConjugation u b-b‖ := by
  have h₁ := norm_sub_le_norm_sub_add_norm_sub (unitaryConjugation u a)
    (unitaryConjugation u b) a
  have h₂ := norm_sub_le_norm_sub_add_norm_sub (unitaryConjugation u b) b a
  have h₃ := conjugation_distance u a b
  rw [norm_sub_rev b a] at h₂
  linarith

lemma conjugated_unitary_error (v u : unitary A) (a b : A) :
    ‖unitaryConjugation (v*u*v⁻¹) b-b‖≤
      ‖unitaryConjugation u a-a‖+2*‖unitaryConjugation v a-b‖ := by
  have h := conjugation_change_test (v*u*v⁻¹) b (unitaryConjugation v a)
  have he : unitaryConjugation (v*u*v⁻¹) (unitaryConjugation v a)=
      unitaryConjugation v (unitaryConjugation u a) := by
    rw [conjugation_mul,conjugation_mul,conjugation_inv_cancel']
  rw [he,norm_sub_rev b (unitaryConjugation v a)] at h
  have hd := conjugation_distance v (unitaryConjugation u a) a
  linarith

lemma correction_error (q : Flow (unitary A)) (v : unitary A) (a c : ℝ)
    (bs b₀ bt : A) {δ η : ℝ} (hδ : 0≤δ) (hη : 0≤η)
    (hc : c≠0 → ‖bt-b₀‖≤δ)
    (hq : ∀ z : ℝ,Commute (q z : A) b₀)
    (ha : a≠0 → ‖bs-b₀‖≤δ)
    (hv : ‖unitaryConjugation v bs-b₀‖≤η) :
    ‖unitaryConjugation (correction q v a c) bt-bt‖≤6*δ+2*η := by
  by_cases hc0 : c=0
  · simp only [hc0,correction_zero,conjugation_one,sub_self,norm_zero]
    positivity
  have hinner : ‖unitaryConjugation (q (-a*c)) bs-bs‖≤2*δ := by
    by_cases ha0 : a=0
    · simp only [ha0,neg_zero,zero_mul,q.map_zero,conjugation_one,sub_self,norm_zero]
      positivity
    · exact (JiangSuConstruction.conjugation_near_commuting _ bs b₀ (hq _)).trans
        (mul_le_mul_of_nonneg_left (ha ha0) (by norm_num))
  have hout : ‖unitaryConjugation (q c) bt-bt‖≤2*δ :=
    (JiangSuConstruction.conjugation_near_commuting _ bt b₀ (hq c)).trans
      (mul_le_mul_of_nonneg_left (hc hc0) (by norm_num))
  have hconj := conjugated_unitary_error v (q (-a*c)) bs b₀
  have hchange := conjugation_change_test (v*q (-a*c)*v⁻¹) bt b₀
  have hprod := conjugation_comp_error (q c) (v*q (-a*c)*v⁻¹) bt bt bt
  have he : correction q v a c=q c*(v*q (-a*c)*v⁻¹) := by
    simp only [correction,mul_assoc]
  rw [he]
  linarith [hc hc0]


theorem surgery_control (p q : Flow (unitary A)) (v₀ v₁ v : unitary A)
    (a b c d : ℝ) (as as₀ as₁ bs b₀ b₁ bt : A) {δ η : ℝ}
    (hδ : 0≤δ) (hη : 0≤η)
    (hpa : ∀ z : ℝ,Commute (p z : A) as₁)
    (hqa : ∀ z : ℝ,Commute (q z : A) as₀)
    (hpb : ∀ z : ℝ,Commute (p z : A) b₁)
    (hqb : ∀ z : ℝ,Commute (q z : A) b₀)
    (haa : a≠0 → ‖as-as₀‖≤δ) (hba : b≠0 → ‖as-as₁‖≤δ)
    (hab : a≠0 → ‖bs-b₀‖≤δ) (hbb : b≠0 → ‖bs-b₁‖≤δ)
    (hc : c≠0 → ‖bt-b₀‖≤δ) (hd : d≠0 → ‖bt-b₁‖≤δ)
    (hflip : unitaryConjugation (p 1*q 1) as=bs)
    (hv₀ : ‖unitaryConjugation v₀ bs-b₀‖≤η)
    (hv₁ : ‖unitaryConjugation v₁ bs-b₁‖≤η)
    (hv : ‖unitaryConjugation v bs-bt‖≤η) :
    ‖unitaryConjugation (surgery p q v₀ v₁ v a b c d) as-bt‖≤16*δ+5*η := by
  have hp : ‖unitaryConjugation (p b) as-as‖≤2*δ := by
    by_cases hb : b=0
    · simp [hb,conjugation_one,mul_nonneg (by norm_num : (0:ℝ)≤2) hδ]
    · exact (JiangSuConstruction.conjugation_near_commuting _ as as₁ (hpa b)).trans
        (mul_le_mul_of_nonneg_left (hba hb) (by norm_num))
  have hq : ‖unitaryConjugation (q a) as-as‖≤2*δ := by
    by_cases ha : a=0
    · simp [ha,conjugation_one,mul_nonneg (by norm_num : (0:ℝ)≤2) hδ]
    · exact (JiangSuConstruction.conjugation_near_commuting _ as as₀ (hqa a)).trans
        (mul_le_mul_of_nonneg_left (haa ha) (by norm_num))
  have hR : ‖unitaryConjugation (p b*q a) as-as‖≤4*δ := by
    have h := conjugation_comp_error (p b) (q a) as as as
    linarith
  have hC := correction_error q v₀ a c bs b₀ bt hδ hη hc hqb hab hv₀
  have hD := correction_error p v₁ b d bs b₁ bt hδ hη hd hpb hbb hv₁
  have hDC := conjugation_comp_error (correction p v₁ b d) (correction q v₀ a c) bt bt bt
  have hVF := conjugation_comp_error v (p 1*q 1) as bs bt
  rw [hflip,sub_self,norm_zero,zero_add] at hVF
  have hVFR := conjugation_comp_error (v*(p 1*q 1)) (p b*q a) as as bt
  have hAll := conjugation_comp_error (correction p v₁ b d*correction q v₀ a c)
    (v*(p 1*q 1)*(p b*q a)) as bt bt
  have he : surgery p q v₀ v₁ v a b c d=
      (correction p v₁ b d*correction q v₀ a c)*(v*(p 1*q 1)*(p b*q a)) := by
    simp only [surgery,mul_assoc]
  rw [he]
  linarith

end FourEdgeSurgery

end

end OAI
