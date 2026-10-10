import Mathlib
import OAI.Probability.SKGap.Localization.RecipeCoefficientClosure
import OAI.Probability.SKGap.Localization.StartedRecipe

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary
variable {n : ℕ} {ι κ ι₀ κ₀ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fintype ι₀] [DecidableEq ι₀] [Fintype κ₀] [DecidableEq κ₀]

def argumentSelect (l : ι₀→ι) (p : κ₀→κ) :
    Args (ι:=ι) (κ:=κ)→L[ℝ]Args (ι:=ι₀) (κ:=κ₀) :=
  ContinuousLinearMap.pi (fun q=>ContinuousLinearMap.proj (Sum.map l p q))

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ι₀] [DecidableEq ι₀] [Fintype κ₀] [DecidableEq κ₀] in
@[simp] lemma argumentSelect_apply (l : ι₀→ι) (p : κ₀→κ)
    (u : Args (ι:=ι) (κ:=κ)) (q : ι₀⊕κ₀) :
    argumentSelect l p u q=u (Sum.map l p q) := rfl

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι₀] [DecidableEq κ₀] in
lemma argumentSelect_norm (l : ι₀→ι) (p : κ₀→κ) : ‖argumentSelect l p‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro q
  exact norm_le_pi_norm u (Sum.map l p q)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ι₀] [DecidableEq ι₀] [Fintype κ₀] [DecidableEq κ₀] in
lemma argumentSelect_local (l : ι₀→ι) (p : κ₀→κ)
    (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (i : Fin n) :
    argumentSelect l p (localArgs H θ x i)=localArgs (H∘l) (θ∘p) x i := by
  ext q;cases q <;> rfl

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι₀] [DecidableEq κ₀] in
lemma SegmentRegular.argumentPullback (l : ι₀→ι) (p : κ₀→κ)
    {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι₀) (κ:=κ₀)→ℝ}
    {F' : Fin n→Args (ι:=ι₀) (κ:=κ₀)→Args (ι:=ι₀) (κ:=κ₀)→L[ℝ]ℝ}
    {x : Spin n} {C : ℝ} (h : SegmentRegular (H∘l) (θ∘p) F F' x C) :
    SegmentRegular H θ (fun i u=>F i (argumentSelect l p u))
      (fun i u=>(F' i (argumentSelect l p u)).comp (argumentSelect l p)) x C := by
  let P:=argumentSelect l p
  have hp : ‖P‖≤1:=argumentSelect_norm l p
  have hn (G : Args (ι:=ι₀) (κ:=κ₀)→L[ℝ]ℝ) : ‖G.comp P‖≤‖G‖ :=
    (G.opNorm_comp_le P).trans (by simpa using mul_le_mul_of_nonneg_left hp (norm_nonneg G))
  have hs (i k : Fin n) (t : ℝ) :
      P (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))=
        localArgs (H∘l) (θ∘p) x i+t •
          (localArgs (H∘l) (θ∘p) (flip x k) i-localArgs (H∘l) (θ∘p) x i) := by
    simp [P,map_add,map_smul,map_sub,argumentSelect_local]
  refine ⟨h.nonneg,?_,?_,?_⟩
  · intro i k t ht
    have hh:=h.deriv i k t ht
    rw [←hs] at hh
    exact hh.comp
      (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)) P.hasFDerivAt
  · intro i k t ht
    exact (hn _).trans (by rw [hs];exact h.bound i k t ht)
  · intro i k t ht
    rw [←ContinuousLinearMap.sub_comp]
    apply (hn _).trans
    rw [hs,show P (localArgs H θ x i)=localArgs (H∘l) (θ∘p) x i from argumentSelect_local l p H θ x i]
    apply (h.lip i k t ht).trans
    apply mul_le_mul_of_nonneg_left _ h.nonneg
    have hh:=P.le_opNorm (t • (localArgs H θ (flip x k) i-localArgs H θ x i))
    have hh':=hh.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
    simpa only [P,map_smul,map_sub,argumentSelect_local,one_mul] using hh'

namespace OrdinaryData
variable {σ : Type*} [Fintype σ]

def argumentPullback (D : OrdinaryData n ι₀ κ₀ σ) (l : ι₀→ι) (p : κ₀→κ)
    (H U : ι→VectorFields n) (θ : κ→Spin n→ℝ) : OrdinaryData n ι κ σ where
  J:=D.J
  j:=D.j
  H:=H
  predecessor:=U
  θ:=θ
  seed:=D.seed
  seedFunction:=fun a b i u=>D.seedFunction a b i (argumentSelect l p u)
  seedDerivative:=fun a b i u=>(D.seedDerivative a b i (argumentSelect l p u)).comp (argumentSelect l p)
  auxFunction:=fun a b i u=>D.auxFunction a b i (argumentSelect l p u)
  auxDerivative:=fun a b i u=>(D.auxDerivative a b i (argumentSelect l p u)).comp (argumentSelect l p)

omit [Fintype σ] in
lemma CoefficientClass.argumentPullback {D : OrdinaryData n ι₀ κ₀ σ} {N : ℕ}
    {x : Spin n} {K : ℝ} (h : D.CoefficientClass N x K)
    (l : ι₀→ι) (p : κ₀→κ) (H U : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (hH : H∘l=D.H) (hθ : θ∘p=D.θ) :
    (D.argumentPullback l p H U θ).CoefficientClass N x K := by
  refine ⟨h.one_le,?_,?_,?_,?_⟩
  · intro a ha b
    dsimp only [OrdinaryData.argumentPullback]
    apply SegmentRegular.argumentPullback l p
    simpa only [hH,hθ] using h.seedRegular a ha b
  · intro a ha b
    dsimp only [OrdinaryData.argumentPullback]
    apply SegmentRegular.argumentPullback l p
    simpa only [hH,hθ] using h.auxRegular a ha b
  · intro a ha b i k t ht
    dsimp only [OrdinaryData.argumentPullback]
    simpa only [map_add,map_smul,map_sub,argumentSelect_local,hH,hθ] using
      h.seedValue a ha b i k t ht
  · intro a ha b i k t ht
    dsimp only [OrdinaryData.argumentPullback]
    simpa only [map_add,map_smul,map_sub,argumentSelect_local,hH,hθ] using
      h.auxValue a ha b i k t ht
end OrdinaryData
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary
variable {n : ℕ} {ι κ κ₀ σ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fintype κ₀] [DecidableEq κ₀] [Fintype σ]

omit [Fintype ι] [Fintype κ] [Fintype κ₀] in
lemma argumentSelect_single_primary (l : ι) (p : κ₀→κ) (q : ι) :
    argumentSelect (fun _ : Unit=>l) p (Pi.single (.inl q) 1)=
      if q=l then (Pi.single (.inl ()) 1 : Args (ι:=Unit) (κ:=κ₀)) else 0 := by
  by_cases hq : q=l
  · subst q; ext s; cases s with
    | inl s=>cases s;simp [argumentSelect_apply]
    | inr s=>simp [argumentSelect_apply]
  · ext s; cases s with
    | inl s=>cases s;simp [argumentSelect_apply,hq,Ne.symm hq]
    | inr s=>simp [argumentSelect_apply,hq]

namespace OrdinaryData
variable (D : OrdinaryData n Unit κ₀ σ) (l : ι) (p : κ₀→κ)
variable (H U : ι→VectorFields n) (θ : κ→Spin n→ℝ)
variable (hH : H∘(fun _:Unit=>l)=D.H) (hθ : θ∘p=D.θ)
include hH hθ

omit [Fintype σ] in
lemma unitPullback_seedCoefficient (a : ℕ) (s : σ) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).seedCoefficient a s=D.seedCoefficient a s := by
  ext x i
  simp only [seedCoefficient,coefficient,argumentPullback,argumentSelect_local,hH,hθ]

omit [Fintype σ] in
lemma unitPullback_auxCoefficient (a : ℕ) (b : Fin a) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).auxCoefficient a b=D.auxCoefficient a b := by
  ext x i
  simp only [auxCoefficient,coefficient,argumentPullback,argumentSelect_local,hH,hθ]

lemma unitPullback_sourceOf (a : ℕ) (Y : Fin a→VectorFields n) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).sourceOf a Y=D.sourceOf a Y := by
  ext x i
  simp only [sourceOf,unitPullback_seedCoefficient D l p H U θ hH hθ,
    unitPullback_auxCoefficient D l p H U θ hH hθ]
  rfl

omit [Fintype σ] in
lemma unitPullback_seedPartial (a : ℕ) (q : ι) (s : σ) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).seedPartial a q s=
      if q=l then D.seedPartial a () s else 0 := by
  by_cases hq : q=l <;> ext x i <;>
    simp [seedPartial,localPartial,argumentPullback,partialAt,
      ContinuousLinearMap.comp_apply,argumentSelect_local,hH,hθ,argumentSelect_single_primary,hq]

omit [Fintype σ] in
lemma unitPullback_auxPartial (a : ℕ) (q : ι) (b : Fin a) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).auxPartial a q b=
      if q=l then D.auxPartial a () b else 0 := by
  by_cases hq : q=l <;> ext x i <;>
    simp [auxPartial,localPartial,argumentPullback,partialAt,
      ContinuousLinearMap.comp_apply,argumentSelect_local,hH,hθ,argumentSelect_single_primary,hq]

lemma unitPullback_partialOf (a : ℕ) (q : ι) (Y : Fin a→VectorFields n) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).partialOf a q Y=
      if q=l then D.partialOf a () Y else 0 := by
  ext x i
  simp only [partialOf,unitPullback_seedPartial D l p H U θ hH hθ,
    unitPullback_auxPartial D l p H U θ hH hθ]
  by_cases hq : q=l <;> simp [hq,argumentPullback,partialOf]

lemma unitPullback_fieldOf (hU : U l=D.predecessor ()) (a : ℕ) (W Y : Fin a→VectorFields n) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).fieldOf a W Y=D.fieldOf a W Y := by
  ext x i
  simp only [fieldOf,unitPullback_sourceOf D l p H U θ hH hθ,
    unitPullback_partialOf D l p H U θ hH hθ,
    unitPullback_auxCoefficient D l p H U θ hH hθ]
  have hm (q : ι) : siteMean (if q=l then D.partialOf a () Y else 0) x*U q x i=
      if q=l then siteMean (D.partialOf a () Y) x*U l x i else 0 := by
    split_ifs with hq
    · subst q;rfl
    · simp [siteMean]
  simp only [argumentPullback,hm,Finset.sum_ite_eq',Finset.mem_univ,ite_true,hU,Fintype.sum_unique]

lemma unitPullback_started_duplicate (hU : U l=D.predecessor ()) (w y : VectorFields n)
    (x : Spin n) (hw : w x=D.sourceOf 1 (fun _=>y) x)
    (hy : y x=D.fieldOf 1 (fun _=>w) (fun _=>y) x) :
    (D.argumentPullback (fun _:Unit=>l) p H U θ).startedSource w y 1 x=w x ∧
      (D.argumentPullback (fun _:Unit=>l) p H U θ).startedAuxiliary w y 1 x=y x := by
  rw [startedSource_one,startedAuxiliary_one,unitPullback_sourceOf D l p H U θ hH hθ,
    unitPullback_fieldOf D l p H U θ hH hθ hU]
  exact ⟨hw.symm,hy.symm⟩
end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
