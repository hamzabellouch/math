import Mathlib
import OAI.Analysis.Commutator.StinespringKernel

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

namespace Kadison.Stinespring

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem gram_middle_nonneg (φ : A →CP (H →L[ℂ] H)) {ι : Type*} [Fintype ι]
    (a : ι → A) (ξ : ι → H) (k : A) (hk : 0≤k) :
    0 ≤ ∑ i, ∑ j, ⟪ξ i, φ (star (a i)*k*a j) (ξ j)⟫_ℂ := by
  have hs : star (CFC.sqrt k)=CFC.sqrt k := (CFC.sqrt_nonneg k).star_eq
  have he (i j : ι) : star (CFC.sqrt k*a i)*(CFC.sqrt k*a j)=star (a i)*k*a j := by
    rw [star_mul,hs,←mul_assoc, mul_assoc (star (a i)),CFC.sqrt_mul_sqrt_self k hk]
  simpa only [he] using gram_nonneg φ (fun i => CFC.sqrt k*a i) ξ

def middleForm (φ : A →CP (H →L[ℂ] H)) (k : A) (x y : PreSpace φ) : ℂ :=
  (ofPre φ x).sum (fun a ξ => (ofPre φ y).sum (fun b η => ⟪ξ,φ (star a*k*b) η⟫_ℂ))

lemma middleForm_nonneg (φ : A →CP (H →L[ℂ] H)) (k : A) (hk : 0≤k) (x : PreSpace φ) :
    0 ≤ middleForm φ k x x := by
  classical
  have h := gram_middle_nonneg φ (fun i : (ofPre φ x).support => (i : A))
    (fun i : (ofPre φ x).support => (ofPre φ x) i) k hk
  have hi (a : A) : (∑ j : (ofPre φ x).support,
      ⟪ofPre φ x a,φ (star a*k*(j : A)) (ofPre φ x j)⟫_ℂ)=
      ∑ b ∈ (ofPre φ x).support,⟪ofPre φ x a,φ (star a*k*b) (ofPre φ x b)⟫_ℂ :=
    Finset.sum_coe_sort _ (fun b : A => ⟪ofPre φ x a,φ (star a*k*b) (ofPre φ x b)⟫_ℂ)
  simp_rw [hi] at h
  rw [Finset.sum_coe_sort _ (fun a : A => ∑ b ∈ (ofPre φ x).support,
    ⟪ofPre φ x a,φ (star a*k*b) (ofPre φ x b)⟫_ℂ)] at h
  exact h

@[simp] lemma middleForm_sub (φ : A →CP (H →L[ℂ] H)) (k l : A) (x y : PreSpace φ) :
    middleForm φ (k-l) x y=middleForm φ k x y-middleForm φ l x y := by
  classical
  simp [middleForm,Finsupp.sum,mul_sub,sub_mul,Finset.sum_sub_distrib]

@[simp] lemma middleForm_real_one (φ : A →CP (H →L[ℂ] H)) (r : ℝ) (x y : PreSpace φ) :
    middleForm φ (algebraMap ℝ A r) x y=(r : ℂ)*form φ x y := by
  classical
  simp [middleForm,form,Finsupp.sum,Algebra.algebraMap_eq_smul_one,
    ←Complex.coe_smul,Finset.mul_sum]

def leftLinear (φ : A →CP (H →L[ℂ] H)) (a : A) : PreSpace φ →ₗ[ℂ] PreSpace φ :=
  (toPre φ).toLinearMap.comp ((Finsupp.lmapDomain H ℂ (a*·)).comp (ofPre φ).toLinearMap)

lemma form_left (φ : A →CP (H →L[ℂ] H)) (a : A) (x y : PreSpace φ) :
    form φ (leftLinear φ a x) y=middleForm φ (star a) x y := by
  classical
  simp only [form,leftLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,ofPre_toPre,
    Finsupp.lmapDomain_apply]
  rw [Finsupp.sum_mapDomain_index]
  · simp [middleForm,star_mul,mul_assoc]
  · simp [Finsupp.sum]
  · intros; simp [Finsupp.sum,Finset.sum_add_distrib]

lemma form_right (φ : A →CP (H →L[ℂ] H)) (a : A) (x y : PreSpace φ) :
    form φ x (leftLinear φ a y)=middleForm φ a x y := by
  classical
  unfold form middleForm
  simp only [leftLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,ofPre_toPre,
    Finsupp.lmapDomain_apply]
  apply Finsupp.sum_congr
  intro b hb
  rw [Finsupp.sum_mapDomain_index]
  · simp [mul_assoc]
  · simp
  · intros; simp

lemma form_left_left (φ : A →CP (H →L[ℂ] H)) (a : A) (x y : PreSpace φ) :
    form φ (leftLinear φ a x) (leftLinear φ a y)=middleForm φ (star a*a) x y := by
  classical
  rw [form_left]
  simp only [middleForm,leftLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,ofPre_toPre,
    Finsupp.lmapDomain_apply]
  apply Finsupp.sum_congr
  intro b hb
  rw [Finsupp.sum_mapDomain_index]
  · simp [mul_assoc]
  · simp
  · intros; simp

lemma leftLinear_bound (φ : A →CP (H →L[ℂ] H)) (a : A) (x : PreSpace φ) :
    ‖leftLinear φ a x‖≤‖a‖*‖x‖ := by
  have hp := middleForm_nonneg φ (algebraMap ℝ A (‖a‖^2)-star a*a)
    (sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq a)) x
  rw [middleForm_sub,middleForm_real_one,←form_left_left] at hp
  have hf (z : PreSpace φ) : (form φ z z).re=‖z‖^2 :=
    (norm_sq_eq_re_inner (𝕜:=ℂ) z).symm
  have hr := hp.1
  simp only [Complex.zero_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,hf] at hr
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg a) (norm_nonneg x))).mp
  rw [mul_pow]
  linarith

def leftAction (φ : A →CP (H →L[ℂ] H)) (a : A) : PreSpace φ →L[ℂ] PreSpace φ :=
  (leftLinear φ a).mkContinuous ‖a‖ (leftLinear_bound φ a)

@[simp] lemma leftAction_apply (φ : A →CP (H →L[ℂ] H)) (a : A) (x : PreSpace φ) :
    leftAction φ a x=leftLinear φ a x := rfl

end Kadison.Stinespring

end

end
end

end OAI
