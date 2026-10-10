import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConnectedSolvableNilpotentDerived
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixScalarExtension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteRationalLinearModel
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

namespace OAI

/-! # A finite-index subgroup with nilpotent derived group

The topology used here is the concrete polynomial topology pulled back
along a faithful representation. Its connected component has finite index.
No algebraic-group structure theorem is assumed.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

open scoped commutatorElement
variable {G K : Type*} [Group G] [Field K] [IsAlgClosed K] [Group.IsSolvable G]

theorem exists_finiteIndex_nilpotent_commutator_of_injective {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (hinj : Function.Injective ι) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsNilpotent (commutator H) := by
  let : TopologicalSpace G := TopologicalSpace.induced ι inferInstance
  have hι : Topology.IsInducing ι := Topology.IsInducing.induced _
  let : SeparatelyContinuousMul G := hι.separatelyContinuousMul ι
  let : ContinuousInv G := hι.continuousInv (fun g => map_inv ι g)
  let : TopologicalSpace.NoetherianSpace G := hι.noetherianSpace
  let H := separateIdentityComponent G
  have hH : H.FiniteIndex := separateIdentityComponent_finiteIndex
  let : PreconnectedSpace H :=
    Subtype.preconnectedSpace (separateIdentityComponent_preconnected (G := G))
  let : SeparatelyContinuousMul H :=
    Topology.IsInducing.subtypeVal.separatelyContinuousMul H.subtype
  let : ContinuousInv H := Topology.IsInducing.subtypeVal.continuousInv (fun _ => rfl)
  let j := ι.comp H.subtype
  have hj : Continuous j := hι.continuous.comp continuous_subtype_val
  have hjind : Topology.IsInducing j := hι.comp Topology.IsInducing.subtypeVal
  have hc₁ (g : H) : Continuous (fun h : H => ⁅g, h⁆) := by
    apply hjind.continuous_iff.mpr
    simpa only [Function.comp_def, map_commutatorElement] using
      (continuous_commutator_left (j g)).comp hj
  have hc₂ (h : H) : Continuous (fun g : H => ⁅g, h⁆) := by
    apply hjind.continuous_iff.mpr
    simpa only [Function.comp_def, map_commutatorElement] using
      (continuous_commutator_right (j h)).comp hj
  exact ⟨H, hH, connected_solvable_commutator_nilpotent hc₁ hc₂ j hj
    (hinj.comp Subtype.val_injective)⟩

end PolynomialMatrixGroup

theorem FiniteRationalLinearModel.exists_finiteIndex_nilpotent_commutator
    {G : Type} [Group G] [Group.IsSolvable G] (M : FiniteRationalLinearModel G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsNilpotent (commutator H) := by
  let e := (Module.finBasis ℚ M.space).equivFun
  let ρ := PolynomialMatrixGroup.coordinateLinearAction M.action e
  have hρ : Function.Injective ρ := by
    intro g h he
    apply M.faithful
    apply LinearEquiv.ext
    intro v
    apply e.injective
    have hh := congrArg (fun a => PolynomialMatrixGroup.linearAction a (e v)) he
    simpa only [ρ, PolynomialMatrixGroup.coordinateLinearAction_apply, e.symm_apply_apply] using hh
  let f := algebraMap ℚ (AlgebraicClosure ℚ)
  exact PolynomialMatrixGroup.exists_finiteIndex_nilpotent_commutator_of_injective
    ((PolynomialMatrixGroup.scalarExtension f).comp ρ)
    ((PolynomialMatrixGroup.scalarExtension_injective f).comp hρ)

end PolycyclicRecognition

end

end OAI
