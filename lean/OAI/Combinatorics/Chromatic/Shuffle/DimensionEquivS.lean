import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.RestrictionB

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def dimensionEquivS {d e : I → ℕ} (h : d=e) : S d ≃ₐ[ℚ] S e := by
  subst e
  exact AlgEquiv.refl

omit [Fintype I] [DecidableEq I] in
lemma dimensionEquivS_val {d e : I → ℕ} (h : d=e) (f : S d) :
    (dimensionEquivS h f).val=rename (Equiv.sigmaCongrRight
      (fun i=>Equiv.cast (congrArg Fin (congrFun h i)))) f.val := by
  subst e
  change f.val=rename id f.val
  simp only [rename_id,AlgHom.id_apply]

@[reducible] def Vars : SplitTree I → Type u
  | .leaf d => Σ i,Fin (d i)
  | .node l r => l.Vars ⊕ r.Vars

noncomputable def varEquiv : (T : SplitTree I) → T.Vars ≃ (Σ i,Fin (T.dim i))
  | .leaf _ => Equiv.refl _
  | .node l r => (Equiv.sumCongr (varEquiv l) (varEquiv r)).trans
      (cutSplit (firstCut l.dim r.dim))

noncomputable def tensorValue : (T : SplitTree I) → tensor rawFamily T →ₐ[ℚ] MvPolynomial T.Vars ℚ
  | .leaf d => (symmetricSpace d).val
  | .node l r => (tensorEquivSum ℚ _ _ ℚ).toAlgHom.comp
      (Algebra.TensorProduct.map (tensorValue l) (tensorValue r))

omit [Fintype I] [DecidableEq I] in
@[simp] lemma tensorValue_tmul (l r : SplitTree I) (x : tensor rawFamily l) (y : tensor rawFamily r) :
    tensorValue (.node l r) (x ⊗ₜ[ℚ] y)=
      rename Sum.inl (tensorValue l x)*rename Sum.inr (tensorValue r y) := by
  exact RawShuffle.tensorEquivSum_tmul _ _

omit [Fintype I] [DecidableEq I] in
lemma tensorValue_injective (T : SplitTree I) : Function.Injective (tensorValue T) := by
  induction T with
  | leaf d => exact Subtype.val_injective
  | node l r ihl ihr =>
    exact (tensorEquivSum ℚ _ _ ℚ).injective.comp
      (TensorProduct.map_injective_of_flat_flat (tensorValue l).toLinearMap
        (tensorValue r).toLinearMap ihl ihr)

lemma tensorValue_rawRestriction (T : SplitTree I) (f : S T.dim) :
    tensorValue T (rawRestriction T f)=rename T.varEquiv.symm f.val := by
  induction T with
  | leaf d =>
    change f.val=rename id f.val
    simp only [rename_id,AlgHom.id_apply]
  | node l r ihl ihr =>
    have h : ∀ x : S l.dim ⊗[ℚ] S r.dim,
        tensorValue (.node l r) (Algebra.TensorProduct.map (rawRestriction l) (rawRestriction r) x)=
          rename (Sum.map l.varEquiv.symm r.varEquiv.symm) (RawShuffle.tensorValue l.dim r.dim x) := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul x y =>
        rw [Algebra.TensorProduct.map_tmul,tensorValue_tmul,ihl,ihr,
          RawShuffle.tensorValue_tmul,map_mul,rename_rename,rename_rename,rename_rename,rename_rename]
        rfl
      | add x y hx hy => simp only [map_add,hx,hy]
    change tensorValue (.node l r) (Algebra.TensorProduct.map (rawRestriction l) (rawRestriction r)
      (restrictTensor (firstCut l.dim r.dim) f)) = _
    rw [h,RawShuffle.tensorValue_restrictTensor,rename_rename]
    rfl

lemma rawRestriction_regroup {T U : SplitTree I} (h : T.dim=U.dim)
    (e : T.Vars ≃ U.Vars)
    (he : ∀ x, U.varEquiv (e x)=Equiv.sigmaCongrRight
      (fun i=>Equiv.cast (congrArg Fin (congrFun h i))) (T.varEquiv x))
    (f : S T.dim) :
    rename e (tensorValue T (rawRestriction T f))=
      tensorValue U (rawRestriction U ((dimensionEquivS h) f)) := by
  rw [tensorValue_rawRestriction,tensorValue_rawRestriction,dimensionEquivS_val,
    rename_rename,rename_rename]
  congr 2
  funext x
  apply U.varEquiv.injective
  simp only [Function.comp_apply,he,Equiv.apply_symm_apply]

noncomputable def packFiberEquiv (d : I → ℕ) (i : I) :
    {x : (Σ j,Fin (d j)) // x.1=i} ≃ Fin (d i) where
  toFun x := x.property ▸ x.val.2
  invFun x := ⟨⟨i,x⟩,rfl⟩
  left_inv x := by
    rcases x with ⟨⟨j,x⟩,h⟩
    dsimp at h
    subst j
    rfl
  right_inv x := rfl

omit [Fintype I] [DecidableEq I] in
lemma pack_equiv_eq_packAction (d : I → ℕ) (e : Equiv.Perm (Σ i,Fin (d i)))
    (h : ∀ x,(e x).1=x.1) :
    ∃ σ : ∀ i,Equiv.Perm (Fin (d i)), ShufflePolynomiality.packAction (fun i=>Fin (d i)) σ=e := by
  let E : ∀ i,{x : (Σ j,Fin (d j)) // x.1=i} ≃ {x : (Σ j,Fin (d j)) // x.1=i} :=
    fun i => e.subtypeEquiv (by intro x; simp only [h x])
  let σ : ∀ i,Equiv.Perm (Fin (d i)) := fun i =>
    (packFiberEquiv d i).symm.trans ((E i).trans (packFiberEquiv d i))
  refine ⟨σ,?_⟩
  apply Equiv.ext
  rintro ⟨i,x⟩
  exact congrArg Subtype.val ((packFiberEquiv d i).symm_apply_apply
    (E i ⟨⟨i,x⟩,rfl⟩))

omit [Fintype I] [DecidableEq I] in
lemma rename_pack_preserving (d : I → ℕ) (e : Equiv.Perm (Σ i,Fin (d i)))
    (h : ∀ x,(e x).1=x.1) (f : S d) : rename e f.val=f.val := by
  obtain ⟨σ,rfl⟩ := pack_equiv_eq_packAction d e h
  exact f.property σ

lemma rawRestriction_regroup_permuted {T U : SplitTree I} (h : T.dim=U.dim)
    (e : T.Vars ≃ U.Vars) (σ : Equiv.Perm (Σ i,Fin (T.dim i)))
    (hσ : ∀ x,(σ x).1=x.1)
    (he : ∀ x, U.varEquiv (e x)=Equiv.sigmaCongrRight
      (fun i=>Equiv.cast (congrArg Fin (congrFun h i))) (σ (T.varEquiv x)))
    (f : S T.dim) :
    rename e (tensorValue T (rawRestriction T f))=
      tensorValue U (rawRestriction U (dimensionEquivS h f)) := by
  rw [tensorValue_rawRestriction,tensorValue_rawRestriction,dimensionEquivS_val,rename_rename]
  have hf := rename_pack_preserving T.dim σ hσ f
  conv_rhs => arg 2; rw [← hf]
  rw [rename_rename,rename_rename]
  congr 2
  funext x
  apply U.varEquiv.injective
  simp only [Function.comp_apply,he,Equiv.apply_symm_apply]

@[reducible] def packIndex : (T : SplitTree I) → T.Vars → I
  | .leaf _, x => x.1
  | .node l _, .inl x => l.packIndex x
  | .node _ r, .inr x => r.packIndex x

omit [Fintype I] [DecidableEq I] in
lemma varEquiv_fst (T : SplitTree I) (x : T.Vars) : (T.varEquiv x).1=T.packIndex x := by
  induction T with
  | leaf d => rfl
  | node l r ihl ihr =>
    cases x with
    | inl x => exact ihl x
    | inr x => exact ihr x

omit [Fintype I] [DecidableEq I] in
lemma varEquiv_symm_packIndex (T : SplitTree I) (x : Σ i,Fin (T.dim i)) :
    T.packIndex (T.varEquiv.symm x)=x.1 := by
  rw [← varEquiv_fst,Equiv.apply_symm_apply]

lemma rawRestriction_regroup_of_pack_preserving {T U : SplitTree I} (h : T.dim=U.dim)
    (e : T.Vars ≃ U.Vars) (he : ∀ x,U.packIndex (e x)=T.packIndex x)
    (f : S T.dim) :
    rename e (tensorValue T (rawRestriction T f))=
      tensorValue U (rawRestriction U (dimensionEquivS h f)) := by
  let C : (Σ i,Fin (T.dim i)) ≃ (Σ i,Fin (U.dim i)) :=
    Equiv.sigmaCongrRight (fun i=>Equiv.cast (congrArg Fin (congrFun h i)))
  let σ : Equiv.Perm (Σ i,Fin (T.dim i)) :=
    T.varEquiv.symm.trans (e.trans (U.varEquiv.trans C.symm))
  have hσ : ∀ x,(σ x).1=x.1 := by
    intro x
    change (U.varEquiv (e (T.varEquiv.symm x))).1=x.1
    rw [varEquiv_fst,he,varEquiv_symm_packIndex]
  apply rawRestriction_regroup_permuted h e σ hσ
  intro x
  change U.varEquiv (e x)=C (C.symm (U.varEquiv (e (T.varEquiv.symm (T.varEquiv x)))))
  rw [Equiv.symm_apply_apply,Equiv.apply_symm_apply]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
