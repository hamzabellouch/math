import OAI.Algebra.AuslanderReiten.Evaluation.TensorBeta
import OAI.Algebra.AuslanderReiten.Cones.ConcreteTwoConeEvaluation
import OAI.Algebra.AuslanderReiten.Duality.FiniteStableResolutionIso

namespace OAI

noncomputable section
namespace ArExplicit.A
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

def betaFiniteModule : FiniteLeftModule k (A k q) where
  carrier := ModuleCat.of (A k q) (augmentationIdeal q)
  scalar := inferInstance
  tower := inferInstance
  finite := Module.Finite.of_injective ((augmentationIdeal q).subtype.restrictScalars k)
    Subtype.val_injective

def betaHom :
    (HomotopyCategory.quotient _ _).obj ((simpleFiniteModule q).completeCochain (AFrobeniusTrace k q)) ⟶
    (HomotopyCategory.quotient _ _).obj ((betaFiniteModule q).completeCochain (AFrobeniusTrace k q)) :=
  (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q)
    (M := simpleFiniteModule q) (N := betaFiniteModule q) (beta q))

omit [CharP k 2] in
theorem betaHom_ne_zero (hq : 1+q ≠ 0) : betaHom q ≠ 0 := by
  intro hz
  have hh := congrArg
    (FiniteLeftModule.resolutionHomotopyEquiv (AFrobeniusTrace k q)
      (simpleFiniteModule q) (betaFiniteModule q)) hz
  erw [betaHom, FiniteLeftModule.resolutionHomotopyEquiv_map, map_zero] at hh
  exact beta_stable_ne_zero q hq hh

end ArExplicit.A

end

end OAI
