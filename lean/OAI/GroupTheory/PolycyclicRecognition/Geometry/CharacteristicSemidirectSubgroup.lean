import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacteristicCyclicSubgroup

namespace OAI

/-! # A characteristic finite-index base in a semidirect product -/

noncomputable section
namespace PolycyclicRecognition
variable {H D : Type} [Group H] [Group D] (K : Subgroup H) [K.Characteristic]
  (ρ : D →* MulAut H)

def characteristicSemidirectMap :
    (K ⋊[(MulAut.characteristic K).comp ρ] D) →* (H ⋊[ρ] D) :=
  SemidirectProduct.map K.subtype (MonoidHom.id D) (by intro d; ext x; rfl)

theorem characteristicSemidirectMap_injective :
    Function.Injective (characteristicSemidirectMap K ρ) := by
  intro x y h
  apply SemidirectProduct.ext
  · apply Subtype.ext
    exact congrArg (fun z : H ⋊[ρ] D => z.left) h
  · exact congrArg (fun z : H ⋊[ρ] D => z.right) h

theorem mem_characteristicSemidirectMap_range (g : H ⋊[ρ] D) :
    g ∈ (characteristicSemidirectMap K ρ).range ↔ g.left ∈ K := by
  constructor
  · rintro ⟨x, rfl⟩
    exact x.left.property
  · intro hg
    exact ⟨⟨⟨g.left, hg⟩, g.right⟩, rfl⟩

theorem characteristicSemidirectMap_finiteIndex [K.FiniteIndex] :
    (characteristicSemidirectMap K ρ).range.FiniteIndex := by
  let G := H ⋊[ρ] D
  let R := (characteristicSemidirectMap K ρ).range
  let f : H ⧸ K → G ⧸ R := Quotient.map' (fun h : H => (SemidirectProduct.inl h : G)) (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    rw [mem_characteristicSemidirectMap_range]
    simpa only [← map_inv, ← map_mul, SemidirectProduct.left_inl] using hxy)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := Quotient.mk''_surjective q
    refine ⟨QuotientGroup.mk g.left, ?_⟩
    change QuotientGroup.mk (SemidirectProduct.inl g.left : G) = QuotientGroup.mk g
    apply QuotientGroup.eq.mpr
    rw [mem_characteristicSemidirectMap_range]
    simp
  let : Finite (G ⧸ R) := Finite.of_surjective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

end PolycyclicRecognition

end

end OAI
