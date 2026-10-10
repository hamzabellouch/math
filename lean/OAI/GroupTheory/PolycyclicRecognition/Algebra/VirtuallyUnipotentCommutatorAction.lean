import OAI.GroupTheory.PolycyclicRecognition.Algebra.SolvableLinearStructure

namespace OAI

/-! # Uniform commutator-action bounds after passing to finite index

This version retains the action bound even when the original representation
has a kernel, as needed for conjugation on a nilpotent normal subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement
namespace PolynomialMatrixGroup

variable {G K : Type*} [Group G] [Field K] [IsAlgClosed K] [Group.IsSolvable G]

theorem exists_finiteIndex_commutator_words {n : ℕ} (ι : G →* PolynomialMatrixGroup K n) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      ∃ c, ∀ w : List (commutator H), w.length = c →
        actionOperatorWord (fun a : commutator H =>
          (linearAction (ι (a : H))).toLinearMap - 1) w = 0 := by
  let : TopologicalSpace G := TopologicalSpace.induced ι inferInstance
  have hι : Topology.IsInducing ι := Topology.IsInducing.induced _
  let : SeparatelyContinuousMul G := hι.separatelyContinuousMul ι
  let : ContinuousInv G := hι.continuousInv (fun g => map_inv ι g)
  let : TopologicalSpace.NoetherianSpace G := hι.noetherianSpace
  let H := separateIdentityComponent G
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
  exact ⟨H, inferInstance, separateIdentityComponent_finiteIndex,
    connected_solvable_commutator_words hc₁ hc₂ j hj⟩

end PolynomialMatrixGroup

theorem exists_finiteIndex_rational_commutator_words
    {G V : Type*} [Group G] [Group.IsSolvable G] [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (ρ : G →* (V ≃ₗ[ℚ] V)) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      ∃ c, ∀ w : List (commutator H), w.length = c →
        actionOperatorWord (fun a : commutator H => (ρ (a : H)).toLinearMap - 1) w = 0 := by
  let e := (Module.finBasis ℚ V).equivFun
  let ι₀ := PolynomialMatrixGroup.coordinateLinearAction ρ e
  let f := algebraMap ℚ (AlgebraicClosure ℚ)
  let ι := (PolynomialMatrixGroup.scalarExtension f).comp ι₀
  obtain ⟨H, hHn, hHi, c, hc⟩ := PolynomialMatrixGroup.exists_finiteIndex_commutator_words ι
  refine ⟨H, hHn, hHi, c, ?_⟩
  let q := (PolynomialMatrixGroup.scalarVector f).comp e.toAddMonoidHom
  have hq : Function.Injective q :=
    (PolynomialMatrixGroup.scalarVector_injective f).comp e.injective
  have hint (a : commutator H) (v : V) :
      q (((ρ (a : H)).toLinearMap - 1) v) =
        ((PolynomialMatrixGroup.linearAction (ι (a : H))).toLinearMap - 1) (q v) := by
    change q (ρ (a : H) v - v) = PolynomialMatrixGroup.linearAction (ι (a : H)) (q v) - q v
    rw [map_sub]
    congr 1
    change PolynomialMatrixGroup.scalarVector f (e (ρ (a : H) v)) = _
    have he : e (ρ (a : H) v) = PolynomialMatrixGroup.linearAction (ι₀ (a : H)) (e v) := by
      simp only [ι₀, PolynomialMatrixGroup.coordinateLinearAction_apply, e.symm_apply_apply]
    rw [he]
    rw [PolynomialMatrixGroup.scalarVector_action]
    rfl
  intro w hw
  apply LinearMap.ext
  intro v
  apply hq
  rw [LinearMap.zero_apply, map_zero]
  have he := actionOperatorWord_intertwines_function
    (fun a : commutator H => (ρ (a : H)).toLinearMap - 1)
    (fun a : commutator H => (PolynomialMatrixGroup.linearAction (ι (a : H))).toLinearMap - 1)
    q hint w v
  rw [hc w hw] at he
  simpa only [LinearMap.zero_apply] using he

end PolycyclicRecognition

end

end OAI
