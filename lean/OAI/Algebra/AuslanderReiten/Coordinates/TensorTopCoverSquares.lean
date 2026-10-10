import OAI.Algebra.AuslanderReiten.Coordinates.TensorTopNaturality
import OAI.Algebra.AuslanderReiten.Cones.BimoduleTwoConeExact
import OAI.Algebra.AuslanderReiten.Cones.TwoConeExtensionDiagrams

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "D" => bimoduleTwoConeData q
local notation "Q" => sourceData q H

theorem topCover_left (n : ℕ) :
    (bimoduleTopComparison q H n).comp
      (TwoCone.baseStepInclusion Q (source_exact q H) n) =
    (TwoCone.baseStepInclusion D (bimodule_exact q) (n+1)).comp
      (bimoduleTopCokernel q H (n+1)) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    simp only [LinearMap.comp_apply, TwoCone.baseStepInclusion_mk, bimoduleTopCokernel_mk]
    exact (LinearMap.congr_fun (bimoduleTopComparison_chain q H n) x).symm

theorem topCover_right (n : ℕ) :
    ((LinearMap.range ((D).d (n+1))).mkQ).comp (bimoduleTopComparison q H n) =
      (bimoduleTopCokernel q H n).comp ((LinearMap.range ((Q).d n)).mkQ) := by
  apply LinearMap.ext
  intro x
  rfl

end ArExplicit.T

end

end OAI
