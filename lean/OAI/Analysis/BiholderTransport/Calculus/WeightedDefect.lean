import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.FiniteTaylor

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma weighted_defect_taylor (w : ι → ℝ) (p : ι → E) (i : ι)
    {b : E×E → ℝ} {c : ι → E×E → ℝ}
    {B : E×E →L[ℝ] E×E →L[ℝ] ℝ}
    {C : ι → E×E →L[ℝ] E×E →L[ℝ] ℝ}
    {q : E → ℝ} {r : ι → E → ℝ}
    (hb : HasSecondTaylor b ((-innerSL ℝ (∑ j,w j • p j)).comp
      (ContinuousLinearMap.fst ℝ E E)) B)
    (hc : ∀ j, HasSecondTaylor (c j) ((-innerSL ℝ (p j)).comp
      (ContinuousLinearMap.fst ℝ E E)) (C j))
    (hB : ∀ a d:E, B (a,d) (a,d)=q a-2*inner ℝ a d)
    (hC : ∀ j (a d:E), C j (a,d) (a,d)=r j a-2*inner ℝ a d) :
    ∃ D : E×E →L[ℝ] E×E →L[ℝ] ℝ,
      HasSecondTaylor (fun h:E×E => b (h.1,w i • h.2)-
        ∑ j,w j*c j (h.1,if j=i then h.2 else 0)) 0 D ∧
      ∀ a d:E, D (a,d) (a,d)=q a-∑ j,w j*r j a := by
  let J : E×E →L[ℝ] E×E := (ContinuousLinearMap.fst ℝ E E).prod
    (w i • ContinuousLinearMap.snd ℝ E E)
  let K : ι → E×E →L[ℝ] E×E := fun j => (ContinuousLinearMap.fst ℝ E E).prod
    (if j=i then ContinuousLinearMap.snd ℝ E E else 0)
  have HTc : ∀ j, HasSecondTaylor (fun h => w j * c j (K j h))
      (w j • (((-innerSL ℝ (p j)).comp (ContinuousLinearMap.fst ℝ E E)).comp (K j)))
      (w j • pullBilinear (C j) (K j)) := fun j =>
        ((hc j).comp_linear (K j)).const_mul' (w j)
  have HCsum := HasSecondTaylor.sum (f := fun j h => w j*c j (K j h))
    (l := fun j => w j • (((-innerSL ℝ (p j)).comp (ContinuousLinearMap.fst ℝ E E)).comp (K j)))
    (B := fun j => w j • pullBilinear (C j) (K j)) Finset.univ (fun j _ => HTc j)
  have HT := (hb.comp_linear J).sub HCsum
  have hl : (((-innerSL ℝ (∑ j,w j • p j)).comp
      (ContinuousLinearMap.fst ℝ E E)).comp J)-
      (∑ j,w j • (((-innerSL ℝ (p j)).comp
        (ContinuousLinearMap.fst ℝ E E)).comp (K j)))=0 := by
    apply ContinuousLinearMap.ext
    rintro ⟨a,d⟩
    simp only [sub_apply,ContinuousLinearMap.comp_apply,J,K,
      ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',
      sum_apply,smul_apply,smul_eq_mul,neg_apply,
      innerSL_apply_apply,zero_apply,sum_inner,real_inner_smul_left,
      mul_neg,Finset.sum_neg_distrib,sub_self]
  rw [hl] at HT
  refine ⟨pullBilinear B J-∑ j,w j • pullBilinear (C j) (K j),?_,?_⟩
  · convert! HT using 1
    funext h
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j=i <;> simp [K,hj]
  · intro a d
    simp only [sub_apply,sum_apply,smul_apply,smul_eq_mul,
      pullBilinear_apply,J,K,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    rw [hB,real_inner_smul_right]
    have HC : ∀ j, C j (a,(if j=i then ContinuousLinearMap.snd ℝ E E else 0) (a,d))
        (a,(if j=i then ContinuousLinearMap.snd ℝ E E else 0) (a,d))=
        r j a-(if j=i then 2*inner ℝ a d else 0) := by
      intro j
      by_cases hj : j=i <;> simp only [hj,ite_true,ite_false,
        ContinuousLinearMap.coe_snd',zero_apply,hC,inner_zero_right,mul_zero]
    simp_rw [HC,mul_sub]
    rw [Finset.sum_sub_distrib]
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    ring

end WeakMTWTransport

end

end OAI
