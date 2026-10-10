import OAI.NumberTheory.Ostmann.ZeroDensity.ActualZeros

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.ZeroDensity

def principalPrimitive (Q : ℕ) (hQ : 0 < Q) : PrimitiveFamily Q :=
  ⟨⟨0,hQ⟩,⟨1,DirichletCharacter.isPrimitive_one_level_one⟩⟩

theorem primitive_principal_unique (Q : ℕ) (hQ : 0 < Q) (χ : PrimitiveFamily Q)
    (hχ : χ.2.val = 1) : χ = principalPrimitive Q hQ := by
  rcases χ with ⟨⟨q,hq⟩,χ,hprim⟩
  change χ = 1 at hχ
  change χ.conductor = q+1 at hprim
  rw [hχ,DirichletCharacter.conductor_one] at hprim
  have hq0 : q=0 := by omega
  subst q
  subst χ
  rfl

theorem sum_primitiveFamily_split {A : Type*} [AddCommMonoid A]
    (Q : ℕ) (hQ : 0 < Q) (f : PrimitiveFamily Q → A) :
    (∑ χ : PrimitiveFamily Q, f χ) =
      f (principalPrimitive Q hQ)+∑ χ : NonprincipalPrimitiveFamily Q, f χ.val := by
  classical
  let : Unique {χ : PrimitiveFamily Q // χ.2.val = 1} :=
    ⟨⟨⟨principalPrimitive Q hQ,rfl⟩⟩,
      fun χ => Subtype.ext (primitive_principal_unique Q hQ χ.val χ.property)⟩
  have h := Fintype.sum_subtype_add_sum_subtype (fun χ : PrimitiveFamily Q => χ.2.val=1) f
  have hd : (default : {χ : PrimitiveFamily Q // χ.2.val=1}).val =
      principalPrimitive Q hQ := primitive_principal_unique Q hQ _ (default : {χ : PrimitiveFamily Q // χ.2.val=1}).property
  simp only [Fintype.sum_unique, hd] at h
  convert h.symm using 1
  congr 1

theorem totalPrimitiveError_split (Q : ℕ) (hQ : 0 < Q) (φ : ℝ → ℝ) (X : ℝ) :
    totalPrimitiveError Q none φ X =
      ‖smoothError (1 : DirichletCharacter ℂ 1) φ X‖+
        ∑ χ : NonprincipalPrimitiveFamily Q, ‖smoothError χ.val.2.val φ X‖ := by
  rw [totalPrimitiveError_none]
  exact sum_primitiveFamily_split Q hQ (fun χ => ‖smoothError χ.2.val φ X‖)

theorem card_nonprincipalPrimitiveFamily_le (Q : ℕ) :
    Fintype.card (NonprincipalPrimitiveFamily Q) ≤ Q^2 := by
  exact (Fintype.card_le_of_injective
    (fun χ : NonprincipalPrimitiveFamily Q => χ.val) Subtype.val_injective).trans
      (card_primitiveFamily_le Q)

end Ostmann.ZeroDensity

end

end OAI
