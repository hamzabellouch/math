import OAI.Analysis.WeakInfiniteness.NonUnitalClosedRange

namespace OAI

/-! The actual C*-algebra image of a representation and its surjective
range restriction. Nuclearity of this image is a separate mathematical property. -/

noncomputable section

namespace WeakPureInfiniteness

variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]

def representedAlgebra (φ : A →⋆ₐ[ℂ] D) : StarSubalgebra ℂ D := φ.range

instance representedAlgebra_closed (φ : A →⋆ₐ[ℂ] D) :
    IsClosed (representedAlgebra φ : Set D) :=
  nonUnitalStarHom_isClosed_range φ.toNonUnitalStarAlgHom

instance representedAlgebra_cstar (φ : A →⋆ₐ[ℂ] D) : CStarAlgebra (representedAlgebra φ) :=
  StarSubalgebra.cstarAlgebra _

def representedQuotientMap (φ : A →⋆ₐ[ℂ] D) : A →⋆ₐ[ℂ] representedAlgebra φ := φ.rangeRestrict

theorem representedQuotientMap_surjective (φ : A →⋆ₐ[ℂ] D) :
    Function.Surjective (representedQuotientMap φ) := by
  rintro ⟨y, a, ha⟩
  exact ⟨a, Subtype.ext ha⟩

def representedInclusion (φ : A →⋆ₐ[ℂ] D) : representedAlgebra φ →⋆ₐ[ℂ] D :=
  (representedAlgebra φ).subtype

theorem representedInclusion_injective (φ : A →⋆ₐ[ℂ] D) :
    Function.Injective (representedInclusion φ) := Subtype.val_injective

@[simp] theorem representedInclusion_apply (φ : A →⋆ₐ[ℂ] D) (a : representedAlgebra φ) :
    representedInclusion φ a = a.val := rfl

@[simp] theorem representedInclusion_quotientMap (φ : A →⋆ₐ[ℂ] D) (a : A) :
    representedInclusion φ (representedQuotientMap φ a) = φ a := rfl

end WeakPureInfiniteness

end

end OAI
