import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteAlgebraIndependentBound

namespace OAI

/-! # Independent-coordinate bound over a finitely generated coefficient algebra -/

noncomputable section
namespace PolycyclicRecognition
variable {K R C : Type} [Field K] [CommRing R] [CommRing C]
  [Algebra K R] [Algebra K C] [Algebra R C] [IsScalarTower K R C]

theorem algebraicIndependent_card_le_of_finite_module {r n : ℕ} (a : Fin r → R)
    (ha : Algebra.adjoin K (Set.range a) = ⊤) [Module.Finite R C]
    (x : Fin n → C) (hx : AlgebraicIndependent K x) : n ≤ r := by
  let f : R →ₐ[K] C := IsScalarTower.toAlgHom K R C
  let S := f.range
  let ψ : R →ₐ[K] S := f.rangeRestrict
  let : Algebra R S := ψ.toRingHom.toAlgebra
  let : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Module.Finite S C := Module.Finite.of_restrictScalars_finite R S C
  let v : Fin r → C := f ∘ a
  have hS : Algebra.adjoin K (Set.range v) = S := by
    rw [show Set.range v = f '' Set.range a from Set.range_comp f a,
      Algebra.adjoin_image, ha, Algebra.map_top]
  have : Module.Finite (Algebra.adjoin K (Set.range v)) C := hS ▸ inferInstance
  exact algebraicIndependent_card_le_of_finite_adjoin v x hx

end PolycyclicRecognition

end

end OAI
