import OAI.GroupTheory.PolycyclicRecognition.Lattices.JointFixedFactorSystem
import OAI.GroupTheory.PolycyclicRecognition.Lattices.FiniteFixedCocycleSection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialSubalgebraNilpotence

namespace OAI

/-! # Constructed joint-fixed residual data for an actual extension

The residual group is defined by the actual section factors and embeds in the
original extension. The prescribed quotient lifts act unipotently on its
kernel Lie algebra.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

structure JointFixedReductionData (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) (qs : List Q) where
  operators : List (L ≃ₗ⁅ℝ⁆ L)
  semisimple : ∀ S ∈ operators, Module.End.IsSemisimple S.toLinearMap
  commute : ∀ S ∈ operators, ∀ T ∈ operators, Commute S.toLinearMap T.toLinearMap
  sectionMap : E.Section
  normalized : sectionMap 1 = 1
  centralizes : ∀ S ∈ operators, ∀ q, sectionMap q ∈ semisimpleActionCentralizer E S
  factorsFixed : ∀ S ∈ operators, ∀ q r, S (GroupExtensionSection.factor E sectionMap q r) =
    GroupExtensionSection.factor E sectionMap q r
  jordanLifts : ∀ q ∈ qs, ∃ S ∈ operators, ∃ U : L ≃ₗ⁅ℝ⁆ L,
    IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
    (polynomialModelLieEquiv (E.conjAct (sectionMap q)) (hsmooth (sectionMap q))).toLinearMap =
      S.toLinearMap * U.toLinearMap

theorem exists_jointFixedReductionData [IsMulCommutative Q] (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) (qs : List Q) :
    Nonempty (JointFixedReductionData E hsmooth qs) := by
  obtain ⟨ss, hss, hpair, σ, hσ, hcent, hfixed, hlifts⟩ :=
    exists_finite_fixed_cocycle_section E hsmooth qs
  exact ⟨⟨ss, hss, hpair, σ, hσ, hcent, hfixed, hlifts⟩⟩

namespace JointFixedReductionData
variable {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}
  (D : JointFixedReductionData E hsmooth qs)

def action (q : Q) : L ≃ₗ⁅ℝ⁆ L :=
  polynomialModelLieEquiv (E.conjAct (D.sectionMap q)) (hsmooth (D.sectionMap q))

omit [LieRing.IsNilpotent L] in
theorem action_commutes (S : L ≃ₗ⁅ℝ⁆ L) (hS : S ∈ D.operators) (q : Q) :
    Commute S.toLinearMap (D.action q).toLinearMap :=
  (mem_semisimpleActionCentralizer_iff E S _ _).mp (D.centralizes S hS q)

def residualSystem : NonabelianFactorSystem (jointFixedLieSubalgebra D.operators) Q :=
  jointFixedFactorSystem (GroupExtensionSection.factorSystem E D.sectionMap D.normalized)
    D.action (fun _ _ => (polynomialModelLieEquiv_apply _ _ _).symm)
    D.operators D.action_commutes D.factorsFixed

def residualEmbedding : FactorExtension D.residualSystem →* G :=
  jointFixedExtensionEmbedding E D.sectionMap D.normalized D.action
    (fun _ _ => (polynomialModelLieEquiv_apply _ _ _).symm)
    D.operators D.action_commutes D.factorsFixed

omit [LieRing.IsNilpotent L] in
theorem residualEmbedding_injective : Function.Injective D.residualEmbedding :=
  jointFixedExtensionEmbedding_injective E D.sectionMap D.normalized D.action
    (fun _ _ => (polynomialModelLieEquiv_apply _ _ _).symm)
    D.operators D.action_commutes D.factorsFixed

omit [LieRing.IsNilpotent L] in
theorem residual_generator_unipotent (q : Q) (hq : q ∈ qs) :
    IsNilpotent (jointFixedLinearAction D.operators (D.action q)
      (fun S hS => D.action_commutes S hS q) - 1) := by
  obtain ⟨S, hS, U, hU, hSU, hA⟩ := D.jordanLifts q hq
  exact jointFixedLinearAction_unipotent D.operators S U (D.action q) hS
    (fun T hT => D.action_commutes T hT q) hU hSU hA

theorem residual_kernel_nilpotent : Group.IsNilpotent (jointFixedLieSubalgebra D.operators) := by
  let K := jointFixedLieSubalgebra D.operators
  let : LieRing.IsNilpotent K := Function.Injective.lieAlgebra_isNilpotent
    (f := K.incl) Subtype.val_injective
  exact polynomialSubalgebra_group_nilpotent K

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
