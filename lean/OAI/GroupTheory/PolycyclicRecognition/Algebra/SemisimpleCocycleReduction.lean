import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleMovingLang
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ProjectedFactorSystem
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorSystemCocycleReduction

namespace OAI

/-! # Eliminating a moving central component of an extension cocycle

This constructs the projected factor system and an actual kernel correction.
The corrected factors are fixed by S; no splitting of the original extension
or existence of a cocycle correction is assumed.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group Q] [IsMulCommutative Q]

theorem semisimple_cocycle_reduction (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (F : NonabelianFactorSystem (innerCentralizerLieSubalgebra S) Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hSA : ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hact : ∀ q x, (F.action q x : L) = A q x)
    (q₀ : Q) (U : L ≃ₗ⁅ℝ⁆ L) (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : (A q₀).toLinearMap = S.toLinearMap * U.toLinearMap) :
    ∃ b : Q → innerCentralizerLieSubalgebra S, ∃ hb : b 1 = 1,
      ∀ q r, S ((F.gauge b hb).factor q r : L) = ((F.gauge b hb).factor q r : L) := by
  let p := innerCentralizerMovingGroupProjection S hS
  let j := innerCentralizerMovingInclusion S
  have hpj : ∀ x, p (j x) = x := innerCentralizerMovingProjection_section S hS
  have hp : Function.Surjective p := fun x => ⟨j x, hpj x⟩
  let a := fun q => semisimpleMovingGroupAction S (A q) (hSA q)
  have ha : ∀ q x, p (F.action q x) = a q (p x) := by
    intro q x
    have hh : F.action q x = innerCentralizerGroupAction S (A q) (hSA q) x :=
      Subtype.ext (hact q x)
    rw [hh]
    exact movingGroupProjection_equivariant S (A q) hS (hSA q) x
  let R := F.mapSurjective p hp a ha
  have hLang : Function.Bijective (fun x => x⁻¹ * R.action q₀ x) :=
    semisimpleMoving_lang_bijective S U (A q₀) hS hU hSU (hSA q₀) hA
  obtain ⟨b, hb, hc⟩ := factorSystem_cocycle_reduction_of_bijective_lang F R p j hpj ha
    (fun _ _ => rfl) q₀ (fun _ => Commute.all _ _) hLang
  refine ⟨b, hb, fun q r => ?_⟩
  exact (innerCentralizerMovingProjection_eq_one_iff S hS _).mp (hc q r)

end PolycyclicRecognition

end

end OAI
