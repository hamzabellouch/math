import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

section Unital

variable {B : Type*} [CStarAlgebra B] [Nontrivial B]

lemma exists_small_inverse (a : B) {d : ℝ} (had : ‖a‖ ≤ d) (hd : d < 1) :
    ∃ b : B,(1+a)*b=1 ∧ b*(1+a)=1 ∧ ‖b‖ ≤ (1-d)⁻¹ := by
  have ha : ‖-a‖ < 1 := by simpa only [norm_neg] using had.trans_lt hd
  let u := Units.oneSub (-a) ha
  let b : B := ↑u⁻¹
  have hl : (1+a)*b=1 := by simpa only [u,Units.val_oneSub,sub_neg_eq_add] using u.mul_inv
  have hr : b*(1+a)=1 := by simpa only [u,Units.val_oneSub,sub_neg_eq_add] using u.inv_mul
  refine ⟨b,hl,hr,?_⟩
  have he : b=1-a*b := by
    rw [add_mul,one_mul] at hl
    exact (eq_sub_iff_add_eq).mpr hl
  have hb := norm_sub_le (1 : B) (a*b)
  have hn1 : ‖(1 : B)‖ ≤ 1 := norm_one.le
  have hm := norm_mul_le a b
  have hab : ‖a‖*‖b‖ ≤ d*‖b‖ := mul_le_mul_of_nonneg_right had (norm_nonneg b)
  rw [← he] at hb
  rw [inv_eq_one_div]
  change ‖b‖ ≤ 1/(1-d)
  apply (le_div_iff₀ (by linarith : 0 < 1-d)).mpr
  nlinarith

lemma exists_factored_inverse (g a : B) (hg : ‖g‖ ≤ 1) {d : ℝ}
    (had : ‖a‖ ≤ d) (hd : d < 1) :
    ∃ z : B, ‖z‖ ≤ d/(1-d) ∧
      (1+g*a*g)*(1+g*z*g)=1 ∧ (1+g*z*g)*(1+g*a*g)=1 := by
  have hd0 : 0 ≤ d := (norm_nonneg a).trans had
  have hagg : ‖a*g*g‖ ≤ d := by
    calc
      _≤‖a‖*‖g‖*‖g‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _≤d*1*1 := by gcongr
      _=d := by ring
  obtain ⟨b,hl,hr,hb⟩ := exists_small_inverse (a*g*g) hagg hd
  refine ⟨-b*a,?_,?_,?_⟩
  · calc
      ‖-b*a‖≤‖-b‖*‖a‖ := norm_mul_le _ _
      _≤(1-d)⁻¹*d := by rw [norm_neg]; gcongr
      _=d/(1-d) := by ring
  · calc
      _=1+g*a*g-g*((1+a*g*g)*b)*a*g := by noncomm_ring
      _=1 := by rw [hl]; noncomm_ring
  · calc
      _=1+g*a*g-g*(b*(1+a*g*g))*a*g := by noncomm_ring
      _=1 := by rw [hr]; noncomm_ring

lemma norm_one_add_le (a : B) : ‖1+a‖ ≤ 1+‖a‖ := by
  simpa only [norm_one] using norm_add_le (1 : B) a

lemma norm_factored_perturbation_le (g z : B) (hg : ‖g‖ ≤ 1) :
    ‖1+g*z*g‖ ≤ 1+‖z‖ := by
  apply (norm_one_add_le _).trans
  apply add_le_add_right
  calc
    _≤‖g‖*‖z‖*‖g‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _≤1*‖z‖*1 := by gcongr
    _=‖z‖ := by ring

lemma normalized_inverse_difference_bound
    (g z Z Z₁ W W₁ p F C e y : B) {η : ℝ}
    (hη : 0 ≤ η) (hg : ‖g‖ ≤ 1) (hz : ‖z‖ ≤ 1/3) (hZ₁ : ‖Z₁‖ ≤ 9/8)
    (hp : ‖p‖ ≤ 1) (he : ‖e‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (hgself : IsSelfAdjoint g) (hZ : Z=1+g*z*g) (hFCg : F*C*g=p)
    (hZW : Z*star W=1) (hW₁Z₁ : star W₁*Z₁=1)
    (hW : W=W₁+(η : ℂ) • (g*y*g)) :
    ‖F*C*(Z-Z₁)*e‖ ≤ 3/2*η := by
  have hdiff : Z-Z₁= -(η : ℂ) • (Z*g*star y*g*Z₁) := by
    have heq : Z*(star W₁-star W)*Z₁=Z-Z₁ := by
      rw [mul_sub,sub_mul,mul_assoc Z (star W₁) Z₁,hW₁Z₁,hZW,mul_one,one_mul]
    rw [← heq,hW,star_add,star_smul,star_mul,star_mul,hgself.star_eq]
    simp only [Complex.star_def,Complex.conj_ofReal,sub_add_cancel_left,neg_mul,mul_neg,mul_smul_comm,smul_mul_assoc]
    simp only [mul_assoc,neg_smul]
  rw [hdiff,mul_smul_comm,smul_mul_assoc,norm_smul,norm_neg,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hη]
  have halg : F*C*(Z*g*star y*g*Z₁)*e=p*(1+z*g*g)*star y*g*Z₁*e := by
    rw [hZ,← hFCg]
    noncomm_ring
  rw [halg]
  have hh : ‖1+z*g*g‖ ≤ 4/3 := by
    have hmul : ‖z*g*g‖ ≤ 1/3 := by
      calc
        _≤‖z‖*‖g‖*‖g‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _≤(1/3)*1*1 := by gcongr
        _=1/3 := by ring
    exact (norm_one_add_le _).trans (by linarith)
  have hn : ‖p*(1+z*g*g)*star y*g*Z₁*e‖ ≤ 3/2 := by
    calc
      _≤‖p‖*‖1+z*g*g‖*‖star y‖*‖g‖*‖Z₁‖*‖e‖ := by
        repeat' first | apply (norm_mul_le _ _).trans | apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact le_refl _
      _≤1*(4/3)*1*1*(9/8)*1 := by rw [norm_star]; gcongr
      _=3/2 := by norm_num
  nlinarith

end Unital

end

end WeakPureInfiniteness
end

end OAI
