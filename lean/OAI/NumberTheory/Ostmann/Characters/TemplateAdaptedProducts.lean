import OAI.NumberTheory.Ostmann.Characters.TemplateAdaptedCoordinates

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem block_word_factors {R:Type*} [CommMonoid R] (k j:ℕ) (b:Bool)
    (z:WordSlot k (j+1)→R) :
    (∏i:{i:(schedule k j).Slot // (schedule k j).IsCopied j i},
      if hw:(schedule k (j+1)).eligible (.inl (i,b)) ∧
          (schedule k (j+1)).role (.inl (i,b))=.word then z ⟨.inl (i,b),hw⟩ else 1)=
      ∏i:WordSlot k j,splitWords k j b z i := by
  let e : WordSlot k j→{i:(schedule k j).Slot // (schedule k j).IsCopied j i} :=
    fun i=>⟨i.val,word_copied _ _ _ i.property.1 i.property.2⟩
  have hinj : Function.Injective e := by
    intro i i' h
    exact Subtype.ext (congrArg
      (fun x:{i:(schedule k j).Slot // (schedule k j).IsCopied j i}=>x.val) h)
  symm
  apply Fintype.prod_of_injective e hinj
  · intro i hi
    have hw : ¬((schedule k (j+1)).eligible (.inl (i,b)) ∧
        (schedule k (j+1)).role (.inl (i,b))=.word) := by
      intro h
      exact hi ⟨⟨i.val,i.property.1,h.2⟩,rfl⟩
    exact dite_eq_right hw
  · intro i
    have hw : (schedule k (j+1)).eligible (.inl (e i,b)) ∧
        (schedule k (j+1)).role (.inl (e i,b))=.word := ⟨Or.inl i.property.2,i.property.2⟩
    rw [dite_eq_left hw]
    rfl

theorem blockProduct_installWords {R:Type*} [CommMonoid R] (k j:ℕ) (b:Bool)
    (C:(schedule k (j+1)).Slot→R) (z:WordSlot k (j+1)→R) :
    blockProduct k j b (installWords k (j+1) C z)=
      blockProduct k j b C*(∏i:WordSlot k j,splitWords k j b z i) := by
  simp only [blockProduct,installWords,Finset.prod_mul_distrib]
  rw [block_word_factors]

theorem wordTreeEquiv_product {G:Type*} [CommGroup G] (k j:ℕ) (z:WordSlot k j→G) :
    BinaryHaar.product (G:=G) (wordTreeEquiv (G:=G) k j z)=∏i,z i := by
  induction j with
  | zero =>
    let w : WordSlot k 0 := ⟨(.word,true),by simp [schedule,initial,InitialRole.role]⟩
    have : Subsingleton (WordSlot k 0) := ⟨fun i i'=>Subtype.ext
      ((initial_word_unique k i).trans (initial_word_unique k i').symm)⟩
    exact (Fintype.prod_subsingleton z w).symm
  | succ j ih =>
    change BinaryHaar.product (G:=G) (wordTreeEquiv (G:=G) k j (splitWords k j true z))*
      BinaryHaar.product (G:=G) (wordTreeEquiv (G:=G) k j (splitWords k j false z))=∏i,z i
    rw [ih,ih,← Finset.prod_mul_distrib]
    calc
      _ = ∏q:WordSlot k j×Bool,z ((wordEquiv (schedule k j) j).symm q) := by
        simp only [Fintype.prod_prod_type,Fintype.prod_bool,splitWords]
      _ = _ := (wordEquiv (schedule k j) j).symm.prod_comp z

end Ostmann.Characters.Template

end

end OAI
