import OAI.GroupTheory.PolycyclicRecognition.Lattices.JointFixedActionFiltration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InvariantLinearLayer
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratedUnipotentAction

namespace OAI

/-! # The abelian quotient acts on the residual lower-central layers

Inner section factors disappear on these layers, so this is an actual linear
representation of the quotient. Its selected generators are unipotent.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]
  {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}

namespace JointFixedReductionData
variable (D : JointFixedReductionData E hsmooth qs)

abbrev lowerCentralLayer (k : ℕ) := InvariantLinearLayer
  (lowerCentralSeries ℝ (jointFixedLieSubalgebra D.operators) (jointFixedLieSubalgebra D.operators) k).toSubmodule
  (lowerCentralSeries ℝ (jointFixedLieSubalgebra D.operators) (jointFixedLieSubalgebra D.operators) (k + 1)).toSubmodule

def layerEnd (k : ℕ) (q : Q) : Module.End ℝ (D.lowerCentralLayer k) :=
  invariantLayerEnd _ _ (jointFixedLinearAction D.operators (D.action q)
    (fun S hS => D.action_commutes S hS q))
    (jointFixed_action_preserves_lowerCentral D.operators (D.action q)
      (fun S hS => D.action_commutes S hS q) k)
    (jointFixed_action_preserves_lowerCentral D.operators (D.action q)
      (fun S hS => D.action_commutes S hS q) (k + 1))

def layerAction (k : ℕ) : Q →* Module.End ℝ (D.lowerCentralLayer k) where
  toFun := D.layerEnd k
  map_one' := by
    apply LinearMap.ext
    intro y
    refine Quotient.inductionOn' y ?_
    intro x
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply Subtype.ext
    change D.action 1 (x : jointFixedLieSubalgebra D.operators) = (x : L)
    rw [action, polynomialModelLieEquiv_apply, D.normalized, map_one]
    rfl
  map_mul' q r := by
    apply LinearMap.ext
    intro y
    refine Quotient.inductionOn' y ?_
    intro x
    let K := jointFixedLieSubalgebra D.operators
    let R := D.residualSystem
    have hx : (x : K) ∈ lowerCentralSeries ℝ K K k := x.property
    have hy : R.action (q * r) x ∈ lowerCentralSeries ℝ K K k :=
      jointFixed_action_preserves_lowerCentral D.operators (D.action (q * r))
        (fun S hS => D.action_commutes S hS _) k x hx
    have hh := polynomialSubalgebra_inner_difference K (R.factor q r) k (R.action (q * r) x) hy
    rw [← R.action_mul_apply] at hh
    symm
    apply (Submodule.Quotient.eq _).mpr
    exact hh

omit [LieRing.IsNilpotent L] in
theorem layer_generator_unipotent (k : ℕ) (q : Q) (hq : q ∈ qs) :
    IsNilpotent (D.layerAction k q - 1) :=
  invariantLayerEnd_unipotent _ _ _
    (jointFixed_action_preserves_lowerCentral D.operators (D.action q)
      (fun S hS => D.action_commutes S hS q) k)
    (jointFixed_action_preserves_lowerCentral D.operators (D.action q)
      (fun S hS => D.action_commutes S hS q) (k + 1))
    (D.residual_generator_unipotent q hq)

omit [LieRing.IsNilpotent L] in
theorem layer_action_filtration [IsMulCommutative Q]
    (hgen : Subgroup.closure {q | q ∈ qs} = ⊤) (k : ℕ) :
    ∃ c, linearActionFiltration (fun q => D.layerAction k q - 1) c = ⊥ :=
  unipotent_generated_abelian_action_filtration (D.layerAction k) qs hgen
    (D.layer_generator_unipotent k)

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
