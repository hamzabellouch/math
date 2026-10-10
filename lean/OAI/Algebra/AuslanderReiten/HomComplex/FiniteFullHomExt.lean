import OAI.Algebra.AuslanderReiten.HomComplex.FiniteFullHomZero
import OAI.Algebra.AuslanderReiten.HomComplex.PositiveFullHomProducts
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomDegreeProducts
import OAI.Algebra.AuslanderReiten.Ext.ExtIsoCongr

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.FiniteLeftModule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
open CompleteComparison
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)

def fullPositiveModuleExtEquiv (n : ℕ) :
    CohomologyClass (M.completeCochain τ) (M.completeCochain τ) ((n+1:ℕ):ℤ) ≃ₗ[k]
      Ext M.carrier M.carrier (n+1) :=
  (fullPositiveExtEquiv (k := k) _ _ (M.completeCochain_totallyAcyclic τ).to_chain
    (M.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex n).trans
      (selfExtIso (k := k) (M.fullCokernelEquiv τ).toModuleIso (n+1))

theorem fullPositiveModuleExtEquiv_product (n m : ℕ)
    (x : CohomologyClass (M.completeCochain τ) (M.completeCochain τ) ((n+1:ℕ):ℤ))
    (y : CohomologyClass (M.completeCochain τ) (M.completeCochain τ) ((m+1:ℕ):ℤ)) :
    fullPositiveModuleExtEquiv τ M (n+1+m)
      (TateKoszul.degreeEquiv (k := k) (CohomologyClass (M.completeCochain τ) (M.completeCochain τ))
        (show ((n+1:ℕ):ℤ)+((m+1:ℕ):ℤ)=((n+1+m+1:ℕ):ℤ) by omega) (fullHomProduct x y)) =
      (fullPositiveModuleExtEquiv τ M n x).comp (fullPositiveModuleExtEquiv τ M m y) (by omega) := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y,rfl⟩ := CohomologyClass.mk_surjective y
  rw [fullHomProduct_degree_mk _ x y (ResolutionProducts.natCocycleProduct x y) rfl]
  change selfExtIso _ _ (fullPositiveExtEquiv _ _ _ _ _ _) =
    (selfExtIso _ _ (fullPositiveExtEquiv _ _ _ _ _ _)).comp
      (selfExtIso _ _ (fullPositiveExtEquiv _ _ _ _ _ _)) _
  rw [← selfExtIso_comp, fullPositiveExtEquiv_product]

end ArExplicit.FiniteLeftModule

end

end OAI
