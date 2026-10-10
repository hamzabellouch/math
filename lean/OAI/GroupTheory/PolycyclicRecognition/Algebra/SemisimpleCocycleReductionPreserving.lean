import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleCocycleReduction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.EquivariantCocycleReduction

namespace OAI

/-! # Moving-central corrections preserve all earlier commuting symmetries -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
attribute [local instance] LieRing.ofAssociativeRing polynomialSubalgebraGroup
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group Q] [IsMulCommutative Q]

theorem semisimple_cocycle_reduction_preserving (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (F : NonabelianFactorSystem (innerCentralizerLieSubalgebra S) Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hSA : ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hact : ∀ q x, (F.action q x : L) = A q x)
    (q₀ : Q) (U : L ≃ₗ⁅ℝ⁆ L) (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : (A q₀).toLinearMap = S.toLinearMap * U.toLinearMap) :
    ∃ b : Q → innerCentralizerLieSubalgebra S, ∃ hb : b 1 = 1,
      (∀ q, LieAlgebra.ad ℝ L (b q : L) = 0) ∧
      (∀ q r, S ((F.gauge b hb).factor q r : L) = ((F.gauge b hb).factor q r : L)) ∧
      ∀ T : L ≃ₗ⁅ℝ⁆ L, Commute S.toLinearMap T.toLinearMap →
        (∀ q, Commute T.toLinearMap (A q).toLinearMap) →
        (∀ q r, T (F.factor q r : L) = (F.factor q r : L)) → ∀ q, T (b q : L) = (b q : L) := by
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
  obtain ⟨b, hb, hc, hj, hequiv⟩ := factorSystem_cocycle_reduction_equivariant F R p j hpj ha
    (fun _ _ => rfl) q₀ (fun _ => Commute.all _ _) hLang
  refine ⟨b, hb, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨x, hx⟩ := hj q
    rw [hx]
    exact x.property.1
  · intro q r
    exact (innerCentralizerMovingProjection_eq_one_iff S hS _).mp (hc q r)
  · intro T hST hTA hTf q
    let TN := innerCentralizerGroupAction S T hST
    let TM := semisimpleMovingGroupAction S T hST
    have hTj : ∀ x, TN.toMonoidHom (j x) = j (TM.toMonoidHom x) := by
      intro x
      apply Subtype.ext
      rfl
    have hTa : ∀ r x, TM.toMonoidHom (R.action r x) = R.action r (TM.toMonoidHom x) := by
      intro r x
      apply Subtype.ext
      exact LinearMap.congr_fun (hTA r).eq x
    have hTc : ∀ r s, TM.toMonoidHom (R.factor r s) = R.factor r s := by
      intro r s
      change TM (p (F.factor r s)) = p (F.factor r s)
      rw [← movingGroupProjection_equivariant S T hS hST]
      have hh : TN (F.factor r s) = F.factor r s := Subtype.ext (hTf r s)
      exact congrArg p hh
    exact congrArg Subtype.val (hequiv TN.toMonoidHom TM.toMonoidHom hTj hTa hTc q)

end PolycyclicRecognition

end

end OAI
