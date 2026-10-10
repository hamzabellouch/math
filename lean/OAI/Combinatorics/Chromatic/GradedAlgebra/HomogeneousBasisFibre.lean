import Mathlib

namespace OAI

section
namespace ElementaryPositivity
open Module
attribute [local instance] Classical.propDecidable
variable {M J K : Type*} [DecidableEq K] [AddCommGroup M] [Module ℚ M]
variable (b : Basis J ℚ M) (degree : J → K) (p : K → Module.End ℚ M)
variable (hp : ∀ k i,p k (b i)=if degree i=k then b i else 0)

include hp in
lemma homogeneousBasis_span (k : K) :
    Submodule.span ℚ (Set.range (fun i : {i : J // degree i=k}=>b i.val))=LinearMap.range (p k) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨b i.val,by rw [hp,ite_eq_left i.property]⟩
  · rintro _ ⟨x,rfl⟩
    have hx := b.mem_span x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i,rfl⟩:=hy
      rw [hp]
      split_ifs with h
      · exact Submodule.subset_span ⟨⟨i,h⟩,rfl⟩
      · exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul r x hx ih => rw [map_smul]; exact Submodule.smul_mem _ r ih

noncomputable def homogeneousBasisFibre (k : K) :
    Basis {i : J // degree i=k} ℚ (LinearMap.range (p k)) :=
  (Basis.span (b.linearIndependent.comp _ Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (homogeneousBasis_span b degree p hp k))

lemma homogeneousBasisFibre_val (k : K) (i : {i : J // degree i=k}) :
    (homogeneousBasisFibre b degree p hp k i).val=b i.val := by
  simp only [homogeneousBasisFibre,Basis.map_apply,Basis.span_apply,LinearEquiv.coe_ofEq_apply,Function.comp_apply]

include b hp in
lemma homogeneousBasis_finite (k : K) [Module.Finite ℚ (LinearMap.range (p k))] :
    Finite {i : J // degree i=k} :=
  Module.Finite.finite_basis (homogeneousBasisFibre b degree p hp k)

include b hp in
lemma homogeneousBasis_finrank (k : K) [Module.Finite ℚ (LinearMap.range (p k))] :
    Module.finrank ℚ (LinearMap.range (p k))=Nat.card {i : J // degree i=k} := by
  let := homogeneousBasis_finite b degree p hp k
  let := Fintype.ofFinite {i : J // degree i=k}
  rw [Module.finrank_eq_card_basis (homogeneousBasisFibre b degree p hp k),Nat.card_eq_fintype_card]
end ElementaryPositivity

end

end OAI
