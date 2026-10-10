import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConnectedQuasiUnipotentAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SolvableLinearStructure

namespace OAI

/-! # Finite-index uniform unipotence of solvable actions

The identity component in the pulled-back polynomial matrix topology is
normal and has finite index. The connected-action theorem applies to it.
Faithfulness of the representation is not required.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

open scoped commutatorElement
variable {G K : Type*} [Group G] [Field K] [IsAlgClosed K]
    [Group.IsSolvable G] [Group.FG G]

theorem exists_finiteIndex_quasiUnipotent_words {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n)
    (hρ : ∀ g, ∃ m : ℕ, 0 < m ∧ IsNilpotent ((linearAction (ι g)).toLinearMap ^ m - 1)) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧ ∃ c : ℕ,
      ∀ w : List H, w.length = c →
        actionOperatorWord (fun a : H => (linearAction (ι a)).toLinearMap - 1) w = 0 := by
  let : TopologicalSpace G := TopologicalSpace.induced ι inferInstance
  have hι : Topology.IsInducing ι := Topology.IsInducing.induced _
  let : SeparatelyContinuousMul G := hι.separatelyContinuousMul ι
  let : ContinuousInv G := hι.continuousInv (fun g => map_inv ι g)
  let : TopologicalSpace.NoetherianSpace G := hι.noetherianSpace
  let H := separateIdentityComponent G
  let : H.FiniteIndex := separateIdentityComponent_finiteIndex
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
  obtain ⟨c, hc⟩ := connected_solvable_quasiUnipotent_words hc₁ hc₂ j hj
    (fun g => hρ g)
  exact ⟨H, inferInstance, inferInstance, c, hc⟩

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
