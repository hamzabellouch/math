import Mathlib
import OAI.Analysis.Commutator.BiprodLinkColumn
import OAI.Analysis.Commutator.ProjectionSchroederBernstein

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.HilbertModuleSB

open HilbertBiprod PartialIsometryOrder

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))

def intertwinerAlgebra : VonNeumannAlgebra (Space H G) where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ ((diagHom φ ψ).range : Set _)
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (Set.centralizer
      (((diagHom φ ψ).range : Set (Space H G →L[ℂ] Space H G)) ∪ star ((diagHom φ ψ).range : Set (Space H G →L[ℂ] Space H G))))) = _
    exact Set.centralizer_centralizer_centralizer _

lemma mem_intertwinerAlgebra (T : Space H G →L[ℂ] Space H G) :
    T∈intertwinerAlgebra φ ψ ↔ ∀ a,block (φ a) (ψ a)*T=T*block (φ a) (ψ a) := by
  change T∈StarSubalgebra.centralizer ℂ ((diagHom φ ψ).range : Set _) ↔ _
  rw [←SetLike.mem_coe,StarSubalgebra.coe_centralizer,StarMemClass.star_coe_eq,Set.union_self]
  constructor
  · intro h a; exact h _ ⟨a,rfl⟩
  · rintro h _ ⟨a,rfl⟩; exact h a

lemma left_mem : left (H:=H) (G:=G) ∈ intertwinerAlgebra φ ψ :=
  (mem_intertwinerAlgebra φ ψ _).mpr (fun scalar => left_commutes (φ scalar) (ψ scalar))

lemma right_mem : right (H:=H) (G:=G) ∈ intertwinerAlgebra φ ψ :=
  (mem_intertwinerAlgebra φ ψ _).mpr (fun scalar => right_commutes (φ scalar) (ψ scalar))

def offDiagonal (V : H →ₗᵢ[ℂ] G) : Space H G →L[ℂ] Space H G :=
  inrL.comp (V.toContinuousLinearMap.comp inlL.adjoint)

lemma offDiagonal_apply (V : H →ₗᵢ[ℂ] G) (x : Space H G) :
    offDiagonal V x=WithLp.toLp 2 (0,V x.ofLp.1) := by
  simp only [offDiagonal,ContinuousLinearMap.comp_apply,adjoint_inlL,inrL_apply]
  rfl

lemma offDiagonal_initial (V : H →ₗᵢ[ℂ] G) :
    star (offDiagonal V)*offDiagonal V=left := by
  change (offDiagonal V).adjoint.comp (offDiagonal V)=left
  simp only [offDiagonal,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  have hr : (inrL (H:=H) (G:=G)).adjoint.comp inrL=1 :=
    (inr (H:=H) (G:=G)).adjoint_comp_self
  have hv := V.adjoint_comp_self
  simp only [ContinuousLinearMap.comp_assoc] at *
  rw [←ContinuousLinearMap.comp_assoc (inrL (H:=H) (G:=G)).adjoint (inrL (H:=H) (G:=G)),hr]
  simp only [ContinuousLinearMap.one_def,ContinuousLinearMap.id_comp]
  rw [←ContinuousLinearMap.comp_assoc V.toContinuousLinearMap.adjoint V.toContinuousLinearMap (inlL (H:=H) (G:=G)).adjoint,hv]
  simp only [ContinuousLinearMap.one_def,ContinuousLinearMap.id_comp,inl_adjoint]

lemma offDiagonal_right (V : H →ₗᵢ[ℂ] G) : right*offDiagonal V=offDiagonal V := by
  ext x
  simp only [mul_apply_eq_comp,offDiagonal_apply,block_apply]
  rfl

lemma offDiagonal_left (V : H →ₗᵢ[ℂ] G) : offDiagonal V*left=offDiagonal V := by
  ext x
  simp only [mul_apply_eq_comp,offDiagonal_apply,block_apply]
  rfl

lemma offDiagonal_mem (V : H →ₗᵢ[ℂ] G)
    (hV : ∀ a x,V (φ a x)=ψ a (V x)) : offDiagonal V∈intertwinerAlgebra φ ψ := by
  apply (mem_intertwinerAlgebra φ ψ _).mpr
  intro a
  ext x
  simp only [mul_apply_eq_comp,offDiagonal_apply,block_apply,map_zero]
  rw [hV]

lemma subEquivalent_of_embedding (V : H →ₗᵢ[ℂ] G)
    (hV : ∀ a x,V (φ a x)=ψ a (V x)) :
    SubEquivalent (intertwinerAlgebra φ ψ) left right := by
  let v := offDiagonal V
  have hi : star v*v=left := offDiagonal_initial V
  have ht : v*star v*v=v := by rw [mul_assoc,hi]; exact offDiagonal_left V
  have hp : IsStarProjection (v*star v) := ⟨by change (v*star v)*(v*star v)=v*star v; rw [←mul_assoc,ht],by simp⟩
  have hle : v*star v≤right := (hp.le_iff_mul_eq_right right_projection).mpr (by
    rw [←mul_assoc,offDiagonal_right])
  exact ⟨⟨v,offDiagonal_mem φ ψ V hV,ht,hi.le,hle⟩,hi⟩

def offDiagonalReverse (V : G →ₗᵢ[ℂ] H) : Space H G →L[ℂ] Space H G :=
  inlL.comp (V.toContinuousLinearMap.comp inrL.adjoint)

lemma offDiagonalReverse_apply (V : G →ₗᵢ[ℂ] H) (x : Space H G) :
    offDiagonalReverse V x=WithLp.toLp 2 (V x.ofLp.2,0) := by
  simp only [offDiagonalReverse,ContinuousLinearMap.comp_apply,adjoint_inrL,inlL_apply]
  rfl

lemma offDiagonalReverse_initial (V : G →ₗᵢ[ℂ] H) :
    star (offDiagonalReverse V)*offDiagonalReverse V=right := by
  change (offDiagonalReverse V).adjoint.comp (offDiagonalReverse V)=right
  simp only [offDiagonalReverse,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  have hr : (inlL (H:=H) (G:=G)).adjoint.comp inlL=1 :=
    (inl (H:=H) (G:=G)).adjoint_comp_self
  have hv := V.adjoint_comp_self
  simp only [ContinuousLinearMap.comp_assoc] at *
  rw [←ContinuousLinearMap.comp_assoc (inlL (H:=H) (G:=G)).adjoint (inlL (H:=H) (G:=G)),hr]
  simp only [ContinuousLinearMap.one_def,ContinuousLinearMap.id_comp]
  rw [←ContinuousLinearMap.comp_assoc V.toContinuousLinearMap.adjoint V.toContinuousLinearMap (inrL (H:=H) (G:=G)).adjoint,hv]
  simp only [ContinuousLinearMap.one_def,ContinuousLinearMap.id_comp,inr_adjoint]

lemma offDiagonalReverse_left (V : G →ₗᵢ[ℂ] H) : left*offDiagonalReverse V=offDiagonalReverse V := by
  ext x
  simp only [mul_apply_eq_comp,offDiagonalReverse_apply,block_apply]
  rfl

lemma offDiagonalReverse_right (V : G →ₗᵢ[ℂ] H) : offDiagonalReverse V*right=offDiagonalReverse V := by
  ext x
  simp only [mul_apply_eq_comp,offDiagonalReverse_apply,block_apply]
  rfl

lemma offDiagonalReverse_mem (V : G →ₗᵢ[ℂ] H)
    (hV : ∀ a x,V (ψ a x)=φ a (V x)) : offDiagonalReverse V∈intertwinerAlgebra φ ψ := by
  apply (mem_intertwinerAlgebra φ ψ _).mpr
  intro a
  ext x
  simp only [mul_apply_eq_comp,offDiagonalReverse_apply,block_apply,map_zero]
  rw [hV]

lemma subEquivalent_of_reverse_embedding (V : G →ₗᵢ[ℂ] H)
    (hV : ∀ a x,V (ψ a x)=φ a (V x)) :
    SubEquivalent (intertwinerAlgebra φ ψ) right left := by
  let v := offDiagonalReverse V
  have hi : star v*v=right := offDiagonalReverse_initial V
  have ht : v*star v*v=v := by rw [mul_assoc,hi]; exact offDiagonalReverse_right V
  have hp : IsStarProjection (v*star v) := ⟨by change (v*star v)*(v*star v)=v*star v; rw [←mul_assoc,ht],by simp⟩
  have hle : v*star v≤left := (hp.le_iff_mul_eq_right left_projection).mpr (by
    rw [←mul_assoc,offDiagonalReverse_left])
  exact ⟨⟨v,offDiagonalReverse_mem φ ψ V hV,ht,hi.le,hle⟩,hi⟩

lemma link_component_isometry (N : VonNeumannAlgebra (Space H G))
    (v : Link N left right) (hi : v.initial=left) :
    Isometry (BiprodLinkColumn.component N v.adjoint) := by
  apply (ContinuousLinearMap.isometry_iff_adjoint_comp_self _).mpr
  rw [BiprodLinkColumn.component_square,Link.adjoint_final,hi]
  have hl : (left (H:=H) (G:=G)).comp inlL=inlL := by ext x; rfl
  rw [hl]
  exact (inl (H:=H) (G:=G)).adjoint_comp_self

lemma link_component_coisometry (N : VonNeumannAlgebra (Space H G))
    (v : Link N left right) (hf : v.final=right) :
    (BiprodLinkColumn.component N v.adjoint).comp
      (BiprodLinkColumn.component N v.adjoint).adjoint=1 := by
  have hl : v.val.comp (left (H:=H) (G:=G))=v.val := v.mul_source left_projection
  have hf' : v.val.comp v.val.adjoint=right := hf
  have hr : (right (H:=H) (G:=G)).comp inrL=inrL := by ext x; rfl
  have hs : v.adjoint.val.adjoint=v.val := by
    change (star v.val).adjoint=v.val
    simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint]
  rw [BiprodLinkColumn.component_adjoint,BiprodLinkColumn.component,hs]
  change (inrL.adjoint.comp (v.val.comp inlL)).comp
    (inlL.adjoint.comp (v.val.adjoint.comp inrL)) = 1
  calc
    _=inrL.adjoint.comp ((v.val.comp left).comp (v.val.adjoint.comp inrL)) := by
      simp only [←inl_adjoint,ContinuousLinearMap.comp_assoc]
    _=inrL.adjoint.comp ((v.val.comp v.val.adjoint).comp inrL) := by
      rw [hl,ContinuousLinearMap.comp_assoc]
    _=1 := by rw [hf',hr]; exact (inr (H:=H) (G:=G)).adjoint_comp_self

theorem exists_unitary_of_embeddings
    (V : H →ₗᵢ[ℂ] G) (W : G →ₗᵢ[ℂ] H)
    (hV : ∀ a x,V (φ a x)=ψ a (V x))
    (hW : ∀ a x,W (ψ a x)=φ a (W x)) :
    ∃ U : H ≃ₗᵢ[ℂ] G, ∀ a x,U (φ a x)=ψ a (U x) := by
  let N := intertwinerAlgebra φ ψ
  obtain ⟨v,hi,hf⟩ := subEquivalent_antisymm N (left_mem φ ψ) left_projection right_projection
    (subEquivalent_of_embedding φ ψ V hV) (subEquivalent_of_reverse_embedding φ ψ W hW)
  let T := BiprodLinkColumn.component N v.adjoint
  let F : H →ₗᵢ[ℂ] G := ⟨T.toLinearMap,
    (AddMonoidHomClass.isometry_iff_norm T).mp (link_component_isometry N v hi)⟩
  have hsur : Function.Surjective F := by
    intro y
    refine ⟨T.adjoint y,?_⟩
    exact congrArg (fun R : G →L[ℂ] G => R y) (link_component_coisometry N v hf)
  refine ⟨LinearIsometryEquiv.ofSurjective F hsur,?_⟩
  intro a x
  have hc : block (φ a) (ψ a)*star v.adjoint.val=star v.adjoint.val*block (φ a) (ψ a) := by
    simpa only [Link.adjoint,star_star] using (mem_intertwinerAlgebra φ ψ v.val).mp v.mem a
  exact congrArg (fun R : H →L[ℂ] G => R x)
    (BiprodLinkColumn.component_intertwines N φ ψ v.adjoint a hc)

end Kadison.HilbertModuleSB

end

end
end

end OAI
