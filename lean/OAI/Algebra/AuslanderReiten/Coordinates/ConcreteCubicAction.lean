import OAI.Algebra.AuslanderReiten.Resolutions.CoverFullHomAction
import OAI.Algebra.AuslanderReiten.Resolutions.SimpleCoverClasses
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedMiddleShift

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "X₀" => A.simpleFiniteModule q
local notation "τ₀" => AFrobeniusTrace k q
local notation "H₀" => fun n => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) n
private abbrev simpleHomotopyObject :=
  (HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)).obj (A.simpleComplete q)
local notation "SX" => simpleHomotopyObject q

theorem evaluatedFirstCokernel_fullHom_action (n : ℕ) (a : ℤ)
    (v : SX ⟶ (evaluatedBaseResolution q (n+3))⟦a⟧) :
    evaluatedBaseFullHomEquiv q n a
      (v ≫ (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ n)⟦a⟧') =
      TateKoszul.degreeEquiv (k := k) H₀
        (by omega : (a-((n+3 : ℕ) : ℤ))+3=a-(n : ℤ))
        (fullHomProduct (evaluatedBaseFullHomEquiv q (n+3) a v) (firstCoverClass q)) := by
  exact coverFullHom_action k (A.simpleComplete q)
    (evaluatedBaseResolution q) (evaluatedBaseStepIso q) (evaluatedBaseZeroResolutionIso q).symm
    (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀)
    (TwoCone.evaluatedFirstCokernel_step D₀ hf₀ (bimodule_exact q)
      (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀)
    (firstCoverClass q) (firstCoverClass_hom q) n a v

theorem evaluatedSecondCokernel_fullHom_action (n : ℕ) (a : ℤ)
    (v : SX ⟶ (evaluatedBaseResolution q (n+3))⟦a⟧) :
    evaluatedBaseFullHomEquiv q n a
      (v ≫ (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ n)⟦a⟧') =
      TateKoszul.degreeEquiv (k := k) H₀
        (by omega : (a-((n+3 : ℕ) : ℤ))+3=a-(n : ℤ))
        (fullHomProduct (evaluatedBaseFullHomEquiv q (n+3) a v) (secondCoverClass q)) := by
  exact coverFullHom_action k (A.simpleComplete q)
    (evaluatedBaseResolution q) (evaluatedBaseStepIso q) (evaluatedBaseZeroResolutionIso q).symm
    (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀)
    (TwoCone.evaluatedSecondCokernel_step D₀ hf₀ (bimodule_exact q)
      (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀)
    (secondCoverClass q) (secondCoverClass_hom q) n a v

end ArExplicit.T

end

end OAI
