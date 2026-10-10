import Mathlib
import OAI.Analysis.WeakInfiniteness.PolarCFC

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

open scoped CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma separation_metric_identity (a b : B) (ha : IsSelfAdjoint a)
    {l : ℝ} (hl : 0 < l) :
    let X := a*b
    let T := star X*X
    let C₁ := a*X*cfc (separationV l) T
    let C₂ := b*cfc (separationR l) T
    star C₁*C₂*cfc (separationG l) T=(l : ℂ) • cfc (separationG l) T := by
  dsimp only
  have hV : IsSelfAdjoint (cfc (separationV l) (star (a*b)*(a*b))) := cfc_predicate _ _
  have hstar : star (a*(a*b)*cfc (separationV l) (star (a*b)*(a*b)))=
      cfc (separationV l) (star (a*b)*(a*b))*star (a*b)*a := by
    rw [star_mul (a*(a*b)) _,star_mul a (a*b),hV.star_eq,ha.star_eq,mul_assoc]
  rw [hstar]
  let X := a*b
  let T := star X*X
  have halg : (cfc (separationV l) T*star X*a)*(b*cfc (separationR l) T)*cfc (separationG l) T=
      cfc (separationV l) T*T*cfc (separationR l) T*cfc (separationG l) T := by
    dsimp only [T,X]
    simp only [mul_assoc]
  rw [halg]
  rw [(Commute.refl T).cfc_real (separationV l) |>.eq]
  have hid : cfc (fun s : ℝ => s) T=T := cfc_id' ℝ T (IsSelfAdjoint.star_mul_self X)
  conv_lhs => lhs; lhs; lhs; rw [← hid]
  rw [cfc_real_mul_three T (IsSelfAdjoint.star_mul_self X) (fun s => s) _ _ continuous_id
    (continuous_separationV hl) (continuous_separationR hl),
    ← cfc_mul (fun s => s*separationV l s*separationR l s) (separationG l) T ((continuous_id.mul (continuous_separationV hl)).mul (continuous_separationR hl)).continuousOn
      (continuous_separationG l).continuousOn]
  have he : cfc (fun s => s*separationV l s*separationR l s*separationG l s) T=
      cfc (fun s => l*separationG l s) T := by
    apply cfc_congr
    intro s hs
    exact separationVRG hl (spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs)
  rw [he,cfc_const_mul l (separationG l) T (continuous_separationG l).continuousOn]
  exact (IsScalarTower.algebraMap_smul ℂ l (cfc (separationG l) T)).symm

omit [PartialOrder B] [StarOrderedRing B] in
lemma compatible_columns_orthogonal (C₁ C₂ g e f Z W w : B) (l : ℝ)
    (he : IsSelfAdjoint e) (hef : e*f=0) (hgf : g*f=f)
    (hW : W=1+g*w*g) (hZW : star Z*W=1)
    (hmetric : star C₁*C₂*g=(l : ℂ) • g) :
    star (C₁*Z*e)*(C₂*W*f)=0 := by
  let D := star C₁*C₂-(l : ℂ) • (1 : B)
  have hDg : D*g=0 := by
    dsimp only [D]
    rw [sub_mul,hmetric,smul_mul_assoc,one_mul,sub_self]
  have hDf : D*f=0 := by rw [← hgf,← mul_assoc,hDg,zero_mul]
  have hDWf : D*W*f=0 := by
    rw [hW,mul_add,mul_one,add_mul,hDf]
    have heq : D*(g*w*g)*f=(D*g)*w*g*f := by simp only [mul_assoc]
    rw [heq,hDg,zero_mul,zero_mul,zero_mul,add_zero]
  have hM : (star C₁*C₂)*W*f=(l : ℂ) • (W*f) := by
    have h : D*W*f=(star C₁*C₂)*W*f-(l : ℂ) • (W*f) := by
      dsimp only [D]
      simp only [sub_mul,smul_mul_assoc,one_mul,mul_assoc]
    rw [h] at hDWf
    exact sub_eq_zero.mp hDWf
  rw [star_mul,star_mul,he.star_eq]
  calc
    _=e*star Z*((star C₁*C₂)*W*f) := by simp only [mul_assoc]
    _=(l : ℂ) • (e*(star Z*W)*f) := by rw [hM]; simp only [mul_smul_comm,mul_assoc]
    _=0 := by rw [hZW,mul_one,hef,smul_zero]

omit [PartialOrder B] [StarOrderedRing B] in
lemma cfc_separationGN (X : B) {l : ℝ} (hl : 0 < l) :
    cfc (separationG l) (star X*X)*cfc (separationN l) (star X*X)=
      cfc (separationN l) (star X*X) := by
  rw [← cfc_mul _ _ _ (continuous_separationG l).continuousOn (continuous_separationN l).continuousOn]
  exact cfc_congr (fun s _ => separationGN hl s)

lemma separation_first_coverage_identity (a X : B) {l : ℝ} (hl : 0 < l) :
    (a*X*cfc (separationV l) (star X*X))*cfc (separationN l) (star X*X)*
      star (X*cfc (separationK l) (star X*X))=
      a*cfc (separationN l) (X*star X) := by
  have hK : IsSelfAdjoint (cfc (separationK l) (star X*X)) := cfc_predicate _ _
  rw [star_mul,hK.star_eq]
  have he : (a*X*cfc (separationV l) (star X*X))*cfc (separationN l) (star X*X)*
      (cfc (separationK l) (star X*X)*star X)=
      a*(X*(cfc (separationV l) (star X*X)*cfc (separationN l) (star X*X)*
        cfc (separationK l) (star X*X))*star X) := by simp only [mul_assoc]
  rw [he,cfc_real_mul_three _ (IsSelfAdjoint.star_mul_self X) _ _ _
    (continuous_separationV hl) (continuous_separationN l) (continuous_separationK hl),
    sandwich_cfc_initial X (fun s => separationV l s*separationN l s*separationK l s) (((continuous_separationV hl).mul (continuous_separationN l)).mul (continuous_separationK hl))]
  congr 1
  apply cfc_congr
  intro s hs
  have h := separation_coverage_VKN hl (spectrum_nonneg_of_nonneg (mul_star_self_nonneg X) hs)
  nlinarith

lemma norm_separation_coverage_factor (X : B) (hX : ‖X‖ ≤ 1)
    {l : ℝ} (hl : 0 < l) :
    ‖X*cfc (separationK l) (star X*X)‖ ≤ (Real.sqrt l)⁻¹ := by
  nontriviality B
  apply norm_mul_cfc_initial_le X _ (continuous_separationK hl) (by positivity)
  intro s hs
  have hs0 := spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs
  have hs1 : s ≤ 1 := by
    have hn : s ≤ ‖star X*X‖ := by
      have h := spectrum.norm_le_norm_of_mem hs
      simpa only [Real.norm_eq_abs,abs_of_nonneg hs0] using h
    rw [CStarRing.norm_star_mul_self] at hn
    nlinarith [norm_nonneg X]
  have h := separation_coverage_K_bound hl hs0 hs1
  simpa only [inv_pow,Real.sq_sqrt hl.le] using h

end

end

end WeakPureInfiniteness
end

end OAI
