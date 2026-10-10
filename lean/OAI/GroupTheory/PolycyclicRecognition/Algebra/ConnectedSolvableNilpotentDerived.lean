import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConnectedSolvableUnipotence

namespace OAI

/-! # Nilpotence of the derived group of a connected solvable matrix group -/

noncomputable section
namespace PolycyclicRecognition

variable {K V H : Type*} [Field K] [AddCommGroup V] [Module K V] [Group H]

theorem nilpotent_of_faithful_action_words (ρ : H →* Module.End K V)
    (hρ : Function.Injective ρ)
    (hw : ∃ c, ∀ w : List H, w.length = c →
      actionOperatorWord (fun h => ρ h - 1) w = 0) : Group.IsNilpotent H := by
  obtain ⟨c, hc⟩ := hw
  have hf := linearActionFiltration_eq_bot_of_word_zero (fun h => ρ h - 1) c hc
  have hle := lowerCentralSeries_le_ker_of_actionFiltration ρ c hf
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  refine ⟨c, eq_bot_iff.mpr ?_⟩
  intro h hh
  change h = 1
  apply hρ
  exact (hle hh).trans ρ.map_one.symm

namespace PolynomialMatrixGroup

open scoped commutatorElement
variable {G : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
    [SeparatelyContinuousMul G] [ContinuousInv G] [Group.IsSolvable G]

theorem connected_solvable_commutator_nilpotent [IsAlgClosed K] {n : ℕ}
    (hc₁ : ∀ g : G, Continuous (fun h : G => ⁅g, h⁆))
    (hc₂ : ∀ h : G, Continuous (fun g : G => ⁅g, h⁆))
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    (hinj : Function.Injective ι) : Group.IsNilpotent (commutator G) := by
  let ρ := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((linearAction.toMonoidHom.comp ι).comp (commutator G).subtype)
  apply nilpotent_of_faithful_action_words ρ
  · intro a b hab
    apply Subtype.ext
    apply hinj
    apply linearAction.injective
    exact LinearEquiv.toLinearMap_injective hab
  · exact connected_solvable_commutator_words hc₁ hc₂ ι hι

theorem exists_finiteIndex_nilpotent_commutator [IsAlgClosed K] {n : ℕ}
    (D : Subgroup (PolynomialMatrixGroup K n)) [Group.IsSolvable D] :
    ∃ H : Subgroup D, H.FiniteIndex ∧ Group.IsNilpotent (commutator H) := by
  let : SeparatelyContinuousMul D :=
    Topology.IsInducing.subtypeVal.separatelyContinuousMul D.subtype
  let : ContinuousInv D := Topology.IsInducing.subtypeVal.continuousInv (fun _ => rfl)
  let : TopologicalSpace.NoetherianSpace D := Topology.IsInducing.subtypeVal.noetherianSpace
  let H := separateIdentityComponent D
  have hH : H.FiniteIndex := separateIdentityComponent_finiteIndex
  let : PreconnectedSpace H :=
    Subtype.preconnectedSpace (separateIdentityComponent_preconnected (G := D))
  let : SeparatelyContinuousMul H :=
    Topology.IsInducing.subtypeVal.separatelyContinuousMul H.subtype
  let : ContinuousInv H := Topology.IsInducing.subtypeVal.continuousInv (fun _ => rfl)
  let ι := D.subtype.comp H.subtype
  have hι : Continuous ι := continuous_subtype_val.comp continuous_subtype_val
  have hc₁ (g : H) : Continuous (fun h : H => ⁅g, h⁆) := by
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    exact (continuous_commutator_left (ι g)).comp hι
  have hc₂ (h : H) : Continuous (fun g : H => ⁅g, h⁆) := by
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    exact (continuous_commutator_right (ι h)).comp hι
  exact ⟨H, hH, connected_solvable_commutator_nilpotent hc₁ hc₂ ι hι
    (Subtype.val_injective.comp Subtype.val_injective)⟩

end PolynomialMatrixGroup
end PolycyclicRecognition

end

end OAI
