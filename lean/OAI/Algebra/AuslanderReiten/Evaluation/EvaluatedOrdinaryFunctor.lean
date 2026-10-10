import OAI.Algebra.AuslanderReiten.Resolutions.EvaluatedOrdinaryResolution
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedQuotientCubic
import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingEvaluationFunctor

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (X : FiniteLeftModule k R)
variable (P : ChainComplex (ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) ℕ)
variable (e : ∀ n, D.term n ≅ P.X n)
local notation "E" => EnvelopingBimodule.evaluationFunctor k R X.carrier

def evaluatedOrdinaryTermIso (n : ℕ) : evaluatedRawTerm D hf X n ≅ (E).obj (P.X n) :=
  (E).mapIso (e n)

omit [Module.Finite k R] in
theorem evaluatedOrdinaryTermIso_square (n : ℕ)
    (he : (e (n+1)).hom ≫ P.d (n+1) n = ModuleCat.ofHom (D.d n) ≫ (e n).hom) :
    (evaluatedOrdinaryTermIso D hf X P e (n+1)).hom ≫ (E).map (P.d (n+1) n) =
      ModuleCat.ofHom (evaluatedBaseDifferential D hf X n) ≫
        (evaluatedOrdinaryTermIso D hf X P e n).hom := by
  have h := congrArg (E).map he
  rw [(E).map_comp, (E).map_comp] at h
  exact h

def evaluatedOrdinaryFunctorIso
    (he : ∀ n, (e (n+1)).hom ≫ P.d (n+1) n = ModuleCat.ofHom (D.d n) ≫ (e n).hom) :
    evaluatedOrdinaryComplex D hf X ≅ ((E).mapHomologicalComplex (ComplexShape.down ℕ)).obj P :=
  HomologicalComplex.Hom.isoOfComponents (evaluatedOrdinaryTermIso D hf X P e)
    (fun i j hij => by
      have h : j+1=i := hij
      subst i
      rw [evaluatedOrdinaryComplex_d]
      exact evaluatedOrdinaryTermIso_square D hf X P e j (he j))

omit [Module.Finite k R] in
theorem evaluatedOrdinaryFunctorIso_comparison
    (he : ∀ n, (e (n+1)).hom ≫ P.d (n+1) n = ModuleCat.ofHom (D.d n) ≫ (e n).hom)
    (m n : ℕ) (d : D.term m ⟶ D.term n) (p : P.X m ⟶ P.X n)
    (hd : d ≫ (e n).hom = (e m).hom ≫ p) :
    (E).map d ≫ (evaluatedOrdinaryFunctorIso D hf X P e he).hom.f n =
      (evaluatedOrdinaryFunctorIso D hf X P e he).hom.f m ≫ (E).map p := by
  have h := congrArg (E).map hd
  rw [(E).map_comp, (E).map_comp] at h
  exact h

end ArExplicit.TwoCone

end

end OAI
