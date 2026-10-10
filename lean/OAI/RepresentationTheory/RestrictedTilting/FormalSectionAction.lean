import OAI.RepresentationTheory.RestrictedTilting.FormalSections
import OAI.RepresentationTheory.RestrictedTilting.FormalLineContinuity

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe u
variable (k : Type u) [Field k]
variable {M : Type u} [AddCommGroup M] [Module k M]
  [Module (MvPolynomial (Fin 2) k) M] [IsScalarTower k (MvPolynomial (Fin 2) k) M]
  [Module.Finite k (M ⧸ planeJetRelation (M := M) k 1)]
variable (σ : Representation k (SL2 k) M) (hσ : PlaneCompatible k σ)
local notation "A" => MvPolynomial (Fin 2) k
local notation "I" => MvPolynomial.idealOfVars (Fin 2) k
local notation "T" => planeJetFD k σ hσ 1

lemma formalPlaneSection_line_action
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1))
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j)
    (g : SL2 k) (F G : M →ₗ[A] A)
    (he : ∀ v, linePolynomial k (F (σ g v)) = linePolynomial k (G v)) (t : T) :
    formalLineMap k (AdicCompletion.map I F (formalPlaneSection k σ hσ s hs ((planeJetFD k σ hσ 1).ρ g t))) =
      formalLineMap k (AdicCompletion.map I G (formalPlaneSection k σ hσ s hs t)) := by
  apply formalLine_map_eq_of_representatives
  intro n
  obtain ⟨v,hv⟩ := (planeJetRelation (M := M) k (n+1)).mkQ_surjective (fdrepLinear k (s n) t)
  refine ⟨σ g v, v, ?_, ?_, he v⟩
  · rw [formalPlaneSection_equivariant, ← hv]
    rfl
  · change planeJetAdicEquiv k (n+1) (fdrepLinear k (s n) t) = _
    rw [← hv]
    rfl
end FiberFunctorProof

end OAI
