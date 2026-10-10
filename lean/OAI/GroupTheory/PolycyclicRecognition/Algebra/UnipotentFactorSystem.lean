import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnipotentExtensionNilpotence
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionConjugation

namespace OAI

/-! # Nilpotence for a smooth factor system with unipotent generators -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group Q] [IsMulCommutative Q]

omit [LieRing.IsNilpotent L] [IsMulCommutative Q] in
theorem factorSystem_conjugation_smooth (R : NonabelianFactorSystem L Q)
    (hR : ∀ q, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (R.action q))
    (g : FactorExtension R) :
    ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ ((FactorExtension.groupExtension R).conjAct g) := by
  have he : ((FactorExtension.groupExtension R).conjAct g : L → L) =
      fun x => g.left * R.action g.right x * g.left⁻¹ :=
    funext (FactorExtension.conjugation_inl R g)
  rw [he]
  exact (contMDiff_const.mul (hR g.right)).mul contMDiff_const

theorem factorSystem_nilpotent_of_unipotent (R : NonabelianFactorSystem L Q)
    (hR : ∀ q, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (R.action q))
    (qs : List Q) (hgen : Subgroup.closure {q | q ∈ qs} = ⊤)
    (hu : ∀ q ∈ qs, ∃ U : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (U.toLinearMap - 1) ∧
      ∀ x, R.action q x = U x) :
    Group.IsNilpotent (FactorExtension R) := by
  let E := FactorExtension.groupExtension R
  let σ : E.Section :=
    { toFun := fun q => ⟨1, q⟩
      rightInverse_rightHom := fun _ => rfl }
  apply extension_nilpotent_of_unipotent_generators E
    (factorSystem_conjugation_smooth R hR) σ rfl qs hgen
  intro q hq
  obtain ⟨U, hU, he⟩ := hu q hq
  have hA : polynomialModelLieEquiv (E.conjAct (σ q))
      (factorSystem_conjugation_smooth R hR (σ q)) = U := by
    ext x
    rw [polynomialModelLieEquiv_apply]
    change E.conjAct (⟨1, q⟩ : FactorExtension R) x = U x
    rw [FactorExtension.conjugation_section]
    exact he x
  rw [hA]
  exact hU

end PolycyclicRecognition

end

end OAI
