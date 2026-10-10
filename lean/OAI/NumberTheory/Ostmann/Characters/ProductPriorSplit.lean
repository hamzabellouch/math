import OAI.NumberTheory.Ostmann.Characters.WordSelection

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Construction

def splitPriorSample {A B I Ω:Type*} (e:A⊕B≃I) (y:B→Ω) (z:A→Ω) : I→Ω :=
  fun i=>Sum.elim z y (e.symm i)

def splitPriorSampleEquiv {A B I Ω:Type*} (e:A⊕B≃I) :
    (B→Ω)×(A→Ω)≃(I→Ω) where
  toFun yz:=splitPriorSample e yz.1 yz.2
  invFun x:=(fun b=>x (e (.inr b)),fun a=>x (e (.inl a)))
  left_inv yz:=by
    rcases yz with ⟨y,z⟩
    simp only [splitPriorSample,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]
  right_inv x:=by
    funext i
    obtain ⟨q,rfl⟩:=e.surjective i
    cases q <;> simp [splitPriorSample]

theorem productPrior_split_mass {A B I Ω:Type*}
    [Fintype A] [Fintype B] [Fintype I] [Fintype Ω]
    [DecidableEq A] [DecidableEq B] [DecidableEq I]
    (e:A⊕B≃I) (μ:I→FinitePrior Ω) (y:B→Ω) (z:A→Ω) :
    (productPrior μ).mass (splitPriorSample e y z)=
      (productPrior (fun b=>μ (e (.inr b)))).mass y*
      (productPrior (fun a=>μ (e (.inl a)))).mass z := by
  change (∏i,(μ i).mass (splitPriorSample e y z i))=_
  rw [← e.prod_comp]
  simp only [splitPriorSample,Equiv.symm_apply_apply,Fintype.prod_sum_type,
    Sum.elim_inl,Sum.elim_inr,productPrior]
  exact mul_comm _ _

theorem productPrior_split_mean {A B I Ω:Type*}
    [Fintype A] [Fintype B] [Fintype I] [Fintype Ω]
    [DecidableEq A] [DecidableEq B] [DecidableEq I]
    (e:A⊕B≃I) (μ:I→FinitePrior Ω) (F:(I→Ω)→ℝ) :
    (productPrior μ).mean F=
      (productPrior (fun b=>μ (e (.inr b)))).mean (fun y=>
        (productPrior (fun a=>μ (e (.inl a)))).mean (fun z=>F (splitPriorSample e y z))) := by
  classical
  unfold FinitePrior.mean
  rw [← (splitPriorSampleEquiv (Ω:=Ω) e).sum_comp
    (fun x=>(productPrior μ).mass x*F x)]
  simp only [Fintype.sum_prod_type,splitPriorSampleEquiv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  change (productPrior μ).mass (splitPriorSample e y z)*F (splitPriorSample e y z)=_
  rw [productPrior_split_mass,mul_assoc]

end Ostmann.Characters

end

end OAI
