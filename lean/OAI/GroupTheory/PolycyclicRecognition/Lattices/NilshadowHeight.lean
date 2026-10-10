import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralNilshadow

namespace OAI

/-! # A fixed linear section of the nilshadow height

The section vectors are the logarithmic coordinates of the actual integral
quotient lifts. The removed action fixes them, as well as the height map.
-/

noncomputable section
namespace PolycyclicRecognition.IntegralNilshadowData
open scoped Manifold ContDiff
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)

def height : D.completion.carrier →* AbelianRealSpace n :=
  (D.completion.exists_height (FactorExtension.groupExtension D.twistedSystem)).choose

theorem height_smooth :
    ContMDiff (𝓘(ℝ, D.completion.carrier)) (𝓘(ℝ, AbelianRealSpace n)) ∞ D.height :=
  (D.completion.exists_height (FactorExtension.groupExtension D.twistedSystem)).choose_spec.1

theorem height_embed (g : FactorExtension D.twistedSystem) :
    D.height (D.completion.embed g) = integralRealHeight g.right :=
  (D.completion.exists_height (FactorExtension.groupExtension D.twistedSystem)).choose_spec.2 g

def heightLinear : D.completion.carrier →ₗ[ℝ] AbelianRealSpace n :=
  (polynomialModelLieHom D.height D.height_smooth).toLinearMap

theorem heightLinear_apply (x : D.completion.carrier) : D.heightLinear x = D.height x :=
  polynomialModelLieHom_apply D.height D.height_smooth x

def quotientBasis (n : ℕ) : Module.Basis (Fin n) ℝ (AbelianRealSpace n) := Pi.basisFun ℝ (Fin n)

def quotientSection : AbelianRealSpace n →ₗ[ℝ] D.completion.carrier :=
  (quotientBasis n).constr ℝ
    (fun i => D.completion.embed ⟨1, integralLatticeGenerator n i⟩)

theorem heightLinear_section (v : AbelianRealSpace n) :
    D.heightLinear (D.quotientSection v) = v := by
  have he : D.heightLinear.comp D.quotientSection = LinearMap.id := by
    apply (quotientBasis n).ext
    intro i
    change D.heightLinear (D.quotientSection ((quotientBasis n) i)) = _
    rw [quotientSection, Module.Basis.constr_basis, heightLinear_apply, height_embed]
    exact integerVectorMap_basis i
  exact LinearMap.congr_fun he v

def completedLieAction (q : IntegralLatticeGroup n) :
    D.completion.carrier ≃ₗ⁅ℝ⁆ D.completion.carrier :=
  polynomialModelLieEquiv (D.completedAction q) (D.completedAction_smooth q)

theorem completedLieAction_height (q : IntegralLatticeGroup n) (x : D.completion.carrier) :
    D.heightLinear (D.completedLieAction q x) = D.heightLinear x := by
  rw [heightLinear_apply, heightLinear_apply]
  change D.height (polynomialModelLieEquiv _ _ x) = D.height x
  rw [polynomialModelLieEquiv_apply]
  apply D.completion.extendedAction_preserves_hom D.integralAction
    D.integralAction_kernel_smooth D.height D.height_smooth
  intro q g
  rw [height_embed, height_embed]
  rfl

theorem completedLieAction_section (q : IntegralLatticeGroup n) (v : AbelianRealSpace n) :
    D.completedLieAction q (D.quotientSection v) = D.quotientSection v := by
  have he : (D.completedLieAction q).toLinearMap.comp D.quotientSection = D.quotientSection := by
    apply (quotientBasis n).ext
    intro i
    change D.completedLieAction q (D.quotientSection ((quotientBasis n) i)) =
      D.quotientSection ((quotientBasis n) i)
    rw [quotientSection, Module.Basis.constr_basis, completedLieAction,
      polynomialModelLieEquiv_apply]
    change D.completion.extendedAction D.integralAction D.integralAction_kernel_smooth q
      (D.completion.embed ⟨1, integralLatticeGenerator n i⟩) = _
    rw [D.completion.extendedAction_embed]
    apply congrArg D.completion.embed
    apply FactorExtension.ext
    · exact map_one (D.removed q)
    · rfl
  exact LinearMap.congr_fun he v

def heightProjection : Module.End ℝ D.completion.carrier :=
  D.quotientSection.comp D.heightLinear

theorem heightLinear_projection (x : D.completion.carrier) :
    D.heightLinear (D.heightProjection x) = D.heightLinear x :=
  D.heightLinear_section _

theorem completedLieAction_projection (q : IntegralLatticeGroup n) (x : D.completion.carrier) :
    D.completedLieAction q (D.heightProjection x) = D.heightProjection x :=
  D.completedLieAction_section q _

theorem projection_completedLieAction (q : IntegralLatticeGroup n) (x : D.completion.carrier) :
    D.heightProjection (D.completedLieAction q x) = D.heightProjection x := by
  change D.quotientSection (D.heightLinear (D.completedLieAction q x)) =
    D.quotientSection (D.heightLinear x)
  rw [D.completedLieAction_height]

end PolycyclicRecognition.IntegralNilshadowData

end

end OAI
