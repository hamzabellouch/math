import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedCoverInitial
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedCoverProducts
import OAI.Algebra.AuslanderReiten.Coordinates.FiniteExtSourceComparison

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
variable (φ : EvaluatedCompleteComparison D hf X hex hr hp τ S e)

theorem evaluatedCover_source (n : ℕ) :
    FiniteLeftModule.HasSourceCoordinates τ S (X.evaluated (baseCokernelModule D hf n)) (n : ℤ)
      ((evaluatedCoverTower D hf X hex hr hp).coverClassFrom τ S
        (CohomologyClass.mk (Cocycle.ofHom (FiniteLeftModule.resolutionMap τ e))) n)
      (evaluatedComparisonCokernel D hf X hex hr hp τ S e φ n) := by
  apply FiniteCoverTower.coverClassFrom_source τ (evaluatedCoverTower D hf X hex hr hp) S
    (CohomologyClass.mk (Cocycle.ofHom (FiniteLeftModule.resolutionMap τ e)))
    (evaluatedComparisonCokernel D hf X hex hr hp τ S e φ)
    (evaluatedComparisonTerm D hf X hex hr hp τ S e φ)
  · exact evaluatedComparison_initial D hf X hex hr hp τ S e φ
  · intro j
    apply LinearMap.ext
    intro z
    rfl
  · intro j
    exact evaluatedComparisonCokernel_inclusion D hf X hex hr hp τ S e φ j

def evaluatedQuotientCocycle (n : ℕ)
    (b : (X.evaluated (baseCokernelModule D hf (n+1))).carrier →ₗ[R] S.carrier) :
    (evaluatedOrdinaryComplex D hf X).X (n+1) ⟶ S.carrier :=
  ModuleCat.ofHom (b.comp (evaluatedBaseQuotient D hf X (n+1)))

omit [CharP k 2] [Module.Finite k R] in
theorem evaluatedQuotientCocycle_closed (n : ℕ)
    (b : (X.evaluated (baseCokernelModule D hf (n+1))).carrier →ₗ[R] S.carrier) :
    (evaluatedOrdinaryComplex D hf X).d (n+2) (n+1) ≫
      evaluatedQuotientCocycle D hf X S n b = 0 := by
  rw [evaluatedOrdinaryComplex_d]
  apply ModuleCat.hom_ext
  change (b.comp (evaluatedBaseQuotient D hf X (n+1))).comp
    (evaluatedBaseDifferential D hf X (n+1)) = 0
  rw [LinearMap.comp_assoc, evaluatedBaseQuotient_comp_d_zero, LinearMap.comp_zero]

include φ in

theorem evaluatedCover_ext (n : ℕ)
    (b : (X.evaluated (baseCokernelModule D hf (n+1))).carrier →ₗ[R] S.carrier) :
    FiniteLeftModule.fullPositiveModuleExtEquiv τ S n
      (fullHomPostcomp (FiniteLeftModule.resolutionMap τ b) ((n+1 : ℕ) : ℤ)
        ((evaluatedCoverTower D hf X hex hr hp).coverClassFrom τ S
          (CohomologyClass.mk (Cocycle.ofHom (FiniteLeftModule.resolutionMap τ e))) (n+1))) =
      (Ext.mk₀ (ModuleCat.ofHom e)).comp
        ((evaluatedOrdinaryResolution D hf X hex hr hp).extMk
          (evaluatedQuotientCocycle D hf X S n b) (n+2) rfl
          (evaluatedQuotientCocycle_closed D hf X S n b)) (zero_add _) := by
  apply FiniteLeftModule.fullPositiveModuleExtEquiv_eq_precomp_extMk τ S
    (X.evaluated (baseCokernelModule D hf 0)).carrier (ModuleCat.ofHom e)
    (evaluatedOrdinaryResolution D hf X hex hr hp) φ n
    (evaluatedQuotientCocycle D hf X S n b) (evaluatedQuotientCocycle_closed D hf X S n b)
    _ (b.comp (evaluatedComparisonCokernel D hf X hex hr hp τ S e φ (n+1)))
  · erw [FiniteLeftModule.resolutionSourceAtStableEquiv_postcomp]
    erw [show FiniteLeftModule.resolutionSourceAtStableEquiv τ S
        (X.evaluated (baseCokernelModule D hf (n+1))) ((n+1 : ℕ) : ℤ) _ =
        StableHom.classOf R _ _ (evaluatedComparisonCokernel D hf X hex hr hp τ S e φ (n+1)) from
      evaluatedCover_source D hf X hex hr hp τ S e φ (n+1), StableHom.postcomp_classOf]
  · intro z
    rfl

end ArExplicit.TwoCone

end

end OAI
