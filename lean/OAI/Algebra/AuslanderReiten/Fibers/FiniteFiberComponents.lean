import OAI.Algebra.AuslanderReiten.Fibers.FiniteEvaluatedFiber

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory
open scoped TensorProduct
universe u
variable {k S : Type u} [Field k] [Ring S] [Algebra k S] [Module.Finite k S]
variable (U V Y : FiniteLeftModule k S)

def fiberSourceInl : U.carrier →ₗ[S] (fiberSource U V Y).carrier :=
  (LinearMap.id : U.carrier →ₗ[S] U.carrier).prod (0 : U.carrier →ₗ[S] V.carrier × Y.canonicalFreeCover.carrier)

def fiberSourceInr : V.carrier →ₗ[S] (fiberSource U V Y).carrier :=
  (0 : V.carrier →ₗ[S] U.carrier).prod
    ((LinearMap.id : V.carrier →ₗ[S] V.carrier).prod (0 : V.carrier →ₗ[S] Y.canonicalFreeCover.carrier))

theorem fiberMap_inl (g : U.carrier ⟶ Y.carrier) (h : V.carrier ⟶ Y.carrier) :
    (fiberMap U V Y g h).hom.comp (fiberSourceInl U V Y) = g.hom := by
  ext x
  change g.hom x + (h.hom 0 + Y.canonicalFreeCoverMap.hom 0) = g.hom x
  simp

theorem fiberMap_inr (g : U.carrier ⟶ Y.carrier) (h : V.carrier ⟶ Y.carrier) :
    (fiberMap U V Y g h).hom.comp (fiberSourceInr U V Y) = h.hom := by
  ext x
  change g.hom 0 + (h.hom x + Y.canonicalFreeCoverMap.hom 0) = h.hom x
  simp

section Evaluation
variable {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
variable (X : FiniteLeftModule k R)
variable (U₁ U₂ Y₀ : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))

theorem middlePairMap_inl :
    (middlePairMap X U₁ U₂ Y₀).comp
      (evaluationMap X (fiberSourceInl U₁ U₂ Y₀)) =
        LinearMap.inl R (evaluated X U₁).carrier (evaluated X U₂).carrier := by
  apply BalancedTensor.leftHom_ext (k := k)
  intro m x
  change (BalancedTensor.tmul (k := k) (R := R) m x,
    BalancedTensor.tmul (k := k) (R := R) (0 : EnvelopingBimodule k R U₂.carrier) x) =
      (BalancedTensor.tmul (k := k) (R := R) m x, 0)
  rw [BalancedTensor.zero_tmul]

theorem middlePairMap_inr :
    (middlePairMap X U₁ U₂ Y₀).comp
      (evaluationMap X (fiberSourceInr U₁ U₂ Y₀)) =
        LinearMap.inr R (evaluated X U₁).carrier (evaluated X U₂).carrier := by
  apply BalancedTensor.leftHom_ext (k := k)
  intro m x
  change (BalancedTensor.tmul (k := k) (R := R) (0 : EnvelopingBimodule k R U₁.carrier) x,
    BalancedTensor.tmul (k := k) (R := R) m x) =
      (0, BalancedTensor.tmul (k := k) (R := R) m x)
  rw [BalancedTensor.zero_tmul]

theorem evaluatedFiberMap_inl (g : U₁.carrier ⟶ Y₀.carrier) (h : U₂.carrier ⟶ Y₀.carrier) :
    (evaluationMap X (fiberMap U₁ U₂ Y₀ g h).hom).comp
      (evaluationMap X (fiberSourceInl U₁ U₂ Y₀)) = evaluationMap X g.hom := by
  rw [← evaluationMap_comp, fiberMap_inl]

theorem evaluatedFiberMap_inr (g : U₁.carrier ⟶ Y₀.carrier) (h : U₂.carrier ⟶ Y₀.carrier) :
    (evaluationMap X (fiberMap U₁ U₂ Y₀ g h).hom).comp
      (evaluationMap X (fiberSourceInr U₁ U₂ Y₀)) = evaluationMap X h.hom := by
  rw [← evaluationMap_comp, fiberMap_inr]

end Evaluation
end ArExplicit.FiniteLeftModule

end

end OAI
