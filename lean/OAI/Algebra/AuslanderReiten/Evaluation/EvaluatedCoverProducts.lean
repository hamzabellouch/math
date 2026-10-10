import OAI.Algebra.AuslanderReiten.Resolutions.FiniteCoverTransport
import OAI.Algebra.AuslanderReiten.Resolutions.EvaluatedOrdinaryResolution
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedCubicCover
import OAI.Algebra.AuslanderReiten.Coordinates.FiniteExtSourceCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (X : FiniteLeftModule k R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))
variable (τ : FrobeniusTrace k R)

def evaluatedCoverTower : FiniteCoverTower (k := k) (R := R) where
  obj n := X.evaluated (baseCokernelModule D hf n)
  middle n := X.evaluated (termModule D hf n)
  inclusion n := evaluatedBaseInclusion D hf hex X n
  quotient n := evaluatedBaseQuotient D hf X n
  injective n := (evaluatedBaseCover_exact D hf hex hr X n).1
  surjective n := (evaluatedBaseCover_exact D hf hex hr X n).2.1
  exact n := (evaluatedBaseCover_exact D hf hex hr X n).2.2
  projective n := by
    let := hp n
    exact FiniteLeftModule.evaluated_projective X (M := termModule D hf n)

theorem evaluatedCoverTower_stepIso (n : ℕ) :
    (evaluatedCoverTower D hf X hex hr hp).stepIso τ n =
      evaluatedBaseSuccessorIso D hf hex hr hp X τ n := by
  apply Iso.ext
  rfl

theorem evaluatedCoverTower_coverClass_hom (n : ℕ) :
    fullHomShiftedHomotopyEquiv k _ _ (n : ℤ)
      ((evaluatedCoverTower D hf X hex hr hp).coverClass τ n) =
        (evaluatedBaseIteration D hf hex hr hp X τ n).hom := by
  rw [FiniteCoverTower.coverClass_hom]
  congr 1

theorem evaluatedCoverTower_coverClassFrom_hom (S : FiniteLeftModule k R)
    (f : S.completeCochain τ ⟶
      (X.evaluated (baseCokernelModule D hf 0)).completeCochain τ) (n : ℕ) :
    fullHomShiftedHomotopyEquiv k _ _ (n : ℤ)
      ((evaluatedCoverTower D hf X hex hr hp).coverClassFrom τ S
        (CohomologyClass.mk (Cocycle.ofHom f)) n) =
      (HomotopyCategory.quotient _ _).map f ≫
        (evaluatedBaseIteration D hf hex hr hp X τ n).hom :=
  FiniteCoverTower.coverClassFrom_hom τ (evaluatedCoverTower D hf X hex hr hp) S f n

end ArExplicit.TwoCone

end

end OAI
