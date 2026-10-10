import OAI.Algebra.AuslanderReiten.Coordinates.ConcreteCubicAction
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedCoverStep
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProductReindex
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProductCoordinate

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "X₀" => A.simpleFiniteModule q
local notation "τ₀" => AFrobeniusTrace k q
local notation "H₀" => fun d => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) d

theorem evaluatedFirstCokernel_step_action (n : ℕ) (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedBaseResolution q (n+2))⟦a⟧) :
    evaluatedBaseFullHomEquiv q n (a+1)
      (ShiftedHom.comp v (evaluatedBaseStepIso q (n+2)).hom (add_comm 1 a) ≫
        (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ n)⟦a+1⟧') =
      TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-((n+2:ℕ):ℤ)+3=(a+1)-(n:ℤ))
        (fullHomProduct (evaluatedBaseFullHomEquiv q (n+2) a v) (firstCoverClass q)) := by
  have h := evaluatedFirstCokernel_fullHom_action q n (a+1)
    (ShiftedHom.comp v (evaluatedBaseStepIso q (n+2)).hom (add_comm 1 a))
  have hs := evaluatedBaseFullHomEquiv_step q (n+2) a v
  exact fullHomProduct_coordinate _ _ (by omega) hs h

theorem evaluatedSecondCokernel_step_action (n : ℕ) (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedBaseResolution q (n+2))⟦a⟧) :
    evaluatedBaseFullHomEquiv q n (a+1)
      (ShiftedHom.comp v (evaluatedBaseStepIso q (n+2)).hom (add_comm 1 a) ≫
        (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ n)⟦a+1⟧') =
      TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-((n+2:ℕ):ℤ)+3=(a+1)-(n:ℤ))
        (fullHomProduct (evaluatedBaseFullHomEquiv q (n+2) a v) (secondCoverClass q)) := by
  have h := evaluatedSecondCokernel_fullHom_action q n (a+1)
    (ShiftedHom.comp v (evaluatedBaseStepIso q (n+2)).hom (add_comm 1 a))
  have hs := evaluatedBaseFullHomEquiv_step q (n+2) a v
  exact fullHomProduct_coordinate _ _ (by omega) hs h

end ArExplicit.T

end

end OAI
