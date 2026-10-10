import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedCoverCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (X : FiniteLeftModule k R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))
variable (τ : FrobeniusTrace k R) (S : FiniteLeftModule k R)
variable (e : S.carrier →ₗ[R] (X.evaluated (baseCokernelModule D hf 0)).carrier)
theorem evaluatedCover_ext_canonical (n : ℕ)
    (b : (X.evaluated (baseCokernelModule D hf (n+1))).carrier →ₗ[R] S.carrier) :
    FiniteLeftModule.fullPositiveModuleExtEquiv τ S n
      (fullHomPostcomp (FiniteLeftModule.resolutionMap τ b) ((n+1 : ℕ) : ℤ)
        ((evaluatedCoverTower D hf X hex hr hp).coverClassFrom τ S
          (CohomologyClass.mk (Cocycle.ofHom (FiniteLeftModule.resolutionMap τ e))) (n+1))) =
      (Ext.mk₀ (ModuleCat.ofHom e)).comp
        ((evaluatedOrdinaryResolution D hf X hex hr hp).extMk
          (evaluatedQuotientCocycle D hf X S n b) (n+2) rfl
          (evaluatedQuotientCocycle_closed D hf X S n b)) (zero_add _) :=
  evaluatedCover_ext D hf X hex hr hp τ S e
    (evaluatedCompleteComparison D hf X hex hr hp τ S e) n b

end ArExplicit.TwoCone

end

end OAI
