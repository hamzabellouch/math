import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.SecondTaylorComposition

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma twist_hasFDerivWithinAt
    {B : E×E → ℝ} {q g : E → E} {p : E} {S A : E →L[ℝ] E} {s : Set E}
    (hB : ContDiffAt ℝ 2 B (0,p))
    (hxx : ∀ u v : E, fderiv ℝ (fderiv ℝ B) (0,p) (u,0) (v,0)=inner ℝ (S u) v)
    (hqx : ∀ u v : E, fderiv ℝ (fderiv ℝ B) (0,p) (0,u) (v,0)= -inner ℝ u v)
    (hq0 : q 0=p) (hqc : ContinuousAt q 0) (hg : HasFDerivWithinAt g A s 0)
    (hcontact : ∀ᶠ x in 𝓝[s] 0, (fderiv ℝ B (x,q x)).comp
      (ContinuousLinearMap.inl ℝ E E)= -(innerSL ℝ (g x)))
    (hcontact0 : (fderiv ℝ B (0,p)).comp
      (ContinuousLinearMap.inl ℝ E E)= -(innerSL ℝ (g 0))) :
    HasFDerivWithinAt q (S+A) s 0 := by
  let J : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let D : E×E → (E →L[ℝ] ℝ) := fun z =>
    (fderiv ℝ B z).comp (ContinuousLinearMap.inl ℝ E E)
  let H : E×E → E×E := fun z => (z.1,-J (D z))
  let L : E×E →L[ℝ] E×E :=
    (ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.snd ℝ E E-S.comp (ContinuousLinearMap.fst ℝ E E))
  let R : E×E →L[ℝ] E×E :=
    (ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.snd ℝ E E+S.comp (ContinuousLinearMap.fst ℝ E E))
  have hRL : Function.LeftInverse R L := by
    intro z
    change (z.1,z.2-S z.1+S z.1)=z
    simp
  have hLR : Function.RightInverse R L := by
    intro z
    change (z.1,z.2+S z.1-S z.1)=z
    simp
  let e : (E×E) ≃L[ℝ] (E×E) := ContinuousLinearEquiv.equivOfInverse L R hRL hLR
  have hDc : ContDiffAt ℝ 1 D (0,p) :=
    (hB.fderiv_right (m := 1) (by norm_num)).clm_comp contDiffAt_const
  have hHc : ContDiffAt ℝ 1 H (0,p) := contDiffAt_fst.prodMk
    (J.contDiff.contDiffAt.comp (0,p) hDc).neg
  have hDd := ((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.clm_comp
      (hasFDerivAt_const (ContinuousLinearMap.inl ℝ E E) (0,p))
  have hHd := (hasFDerivAt_fst (p := (0,p))).prodMk
    (((J.hasFDerivAt).comp (0,p) hDd).neg)
  have hHD : HasFDerivAt H (e : (E×E) →L[ℝ] (E×E)) (0,p) := by
    apply hHd.congr_fderiv
    apply ContinuousLinearMap.ext
    intro z
    apply Prod.ext
    · rfl
    · apply (InnerProductSpace.toDual ℝ E).injective
      change (InnerProductSpace.toDual ℝ E) (-J _) = _
      rw [map_neg,show ∀ ξ : E →L[ℝ] ℝ, (InnerProductSpace.toDual ℝ E) (J ξ)=ξ from
        fun ξ => (InnerProductSpace.toDual ℝ E).apply_symm_apply ξ]
      ext v
      change -((fderiv ℝ B (0,p)) (0,0)+fderiv ℝ (fderiv ℝ B) (0,p) z (v,0)) =
        inner ℝ (z.2-S z.1) v
      rw [show ((0:E),(0:E))=(0:E×E) by rfl,map_zero,zero_add]
      rw [show z=(z.1,0)+(0,z.2) by ext <;> simp,map_add,add_apply,hxx,hqx]
      simp only [inner_sub_left,Prod.fst_add,Prod.snd_add,add_zero,zero_add]
      ring
  have hstrict := hHc.hasStrictFDerivAt' hHD (by norm_num)
  have J_inner (a : E) : J (innerSL ℝ a)=a := by
    apply (InnerProductSpace.toDual ℝ E).injective
    rw [show (InnerProductSpace.toDual ℝ E) (J (innerSL ℝ a))=innerSL ℝ a from
      (InnerProductSpace.toDual ℝ E).apply_symm_apply _]
    rfl
  have hH0 : H (0,p)=(0,g 0) := by
    change (0,-J ((fderiv ℝ B (0,p)).comp (ContinuousLinearMap.inl ℝ E E)))=(0,g 0)
    rw [hcontact0,map_neg,J_inner,neg_neg]
  let inv := hstrict.localInverse H e (0,p)
  have hi : HasFDerivAt inv (e.symm : (E×E) →L[ℝ] (E×E)) (0,g 0) := by
    rw [←hH0]
    exact hstrict.to_localInverse.hasFDerivAt
  have hcomp := hi.comp_hasFDerivWithinAt 0 ((hasFDerivAt_id (𝕜 := ℝ) (0:E)).hasFDerivWithinAt.prodMk hg)
  have hfinal := (hasFDerivAt_snd (p := inv (0,g 0))).comp_hasFDerivWithinAt 0 hcomp
  have heq : ∀ᶠ x in 𝓝[s] 0, q x=(inv (x,g x)).2 := by
    have hnear := (continuousAt_id.prodMk hqc).tendsto.eventually
      (by rw [hq0]; exact hstrict.eventually_left_inverse)
    filter_upwards [hcontact,mem_nhdsWithin_of_mem_nhds hnear] with x hx hxi
    have Hx : H (x,q x)=(x,g x) := by
      change (x,-J ((fderiv ℝ B (x,q x)).comp (ContinuousLinearMap.inl ℝ E E)))=(x,g x)
      rw [hx,map_neg,J_inner,neg_neg]
    change inv (H (x,q x))=(x,q x) at hxi
    rw [Hx] at hxi
    exact (congrArg Prod.snd hxi).symm
  have heq0 : q 0=(inv (0,g 0)).2 := by
    change q 0=(hstrict.localInverse H e (0,p) (0,g 0)).2
    rw [←hH0,hstrict.localInverse_apply_image,hq0]
  apply (hfinal.congr_of_eventuallyEq heq heq0).congr_fderiv
  ext h
  change A h+S h=S h+A h
  exact add_comm _ _

end WeakMTWTransport

end

end OAI
