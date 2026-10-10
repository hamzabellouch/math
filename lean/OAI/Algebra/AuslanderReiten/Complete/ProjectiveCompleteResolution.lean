import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleNaturality

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated

namespace ArExplicit

open CompleteComparison

universe u

variable {R : Type u} [Ring R]

theorem completeCochain_isZero_of_projectiveCokernel
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : TotallyAcyclicCochain K)
    [Module.Projective R (CochainCokernel K)] :
    Limits.IsZero ((HomotopyCategory.quotient _ _).obj K) := by
  let := hK.finite 0
  let : Module.Finite R (CochainCokernel K) := inferInstance
  rw [Limits.IsZero.iff_id_eq_zero]
  apply (cochainHomotopyRawEquiv hK.to_chain hK.to_chain.toExactProjectiveComplex).injective
  rw [map_zero]
  rw [← (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_id,
    cochainHomotopyRawEquiv_map]
  exact StableHom.eq_zero_of_projective_source _

namespace FiniteLeftModule

variable {k : Type u} [Field k] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable (M : FiniteLeftModule k R)

theorem projective_completeCochain_isZero [Module.Projective R M.carrier] :
    Limits.IsZero ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ)) := by
  let : Module.Projective R (CochainCokernel (M.completeCochain τ)) :=
    Module.Projective.of_equiv (M.completeCochainCokernelEquiv τ).symm
  exact completeCochain_isZero_of_projectiveCokernel _ (M.completeCochain_totallyAcyclic τ)

variable {M} {N L : FiniteLeftModule k R}

theorem nonempty_projectiveMiddleShiftIso [Module.Projective R N.carrier]
    (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    Nonempty (((HomotopyCategory.quotient _ _).obj (L.completeCochain τ)) ≅
      ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ))⟦(1 : ℤ)⟧) := by
  obtain ⟨δ, hδ⟩ := exists_resolution_triangle τ f g hf hg hex
  let T := Triangle.mk ((HomotopyCategory.quotient _ _).map (resolutionMap τ f))
    ((HomotopyCategory.quotient _ _).map (resolutionMap τ g)) δ
  have hz : Limits.IsZero T.obj₂ := N.projective_completeCochain_isZero τ
  have : IsIso δ := (T.isZero₂_iff_isIso₃ hδ).mp hz
  exact ⟨asIso δ⟩

def projectiveMiddleShiftIso [Module.Projective R N.carrier]
    (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    ((HomotopyCategory.quotient _ _).obj (L.completeCochain τ)) ≅
      ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ))⟦(1 : ℤ)⟧ := by
  let T := resolutionTriangle τ f g hf hg hex
  have hz : Limits.IsZero T.obj₂ := N.projective_completeCochain_isZero τ
  haveI : IsIso (resolutionConnecting τ f g hf hg hex) :=
    (T.isZero₂_iff_isIso₃ (resolutionTriangle_distinguished τ f g hf hg hex)).mp hz
  exact asIso (resolutionConnecting τ f g hf hg hex)

@[simp]
theorem projectiveMiddleShiftIso_hom [Module.Projective R N.carrier]
    (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    (projectiveMiddleShiftIso τ f g hf hg hex).hom = resolutionConnecting τ f g hf hg hex := rfl

end FiniteLeftModule
end ArExplicit

end

end OAI
