import OAI.Analysis.BoundedHochschild.NormalGNSRepresentation
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

namespace OAI

/-! On bounded sets the faithful normal representation preserves the weak-star
compactness needed to realize limits of the elementary averaging operators. -/

noncomputable section

open Topology
open scoped InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildNormalPart

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def normalGNSWeak (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (F : WeakDual ℂ X) :
    NormalGNS e →WOT[ℂ] NormalGNS e :=
  ContinuousLinearMapWOT.ofCLM (normalGNSRepresentation e (e (WeakDual.toStrongDual F)))

lemma normalGNSWeak_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Continuous (normalGNSWeak e) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro ξ η
  obtain ⟨x, hx⟩ := (mem_normalDual e _).mp (normalGNSRepresentation_coefficients e η ξ)
  have heq : (fun F : WeakDual ℂ X => inner ℂ η (normalGNSWeak e F ξ)) =
      fun F => star (F x) := by
    funext F
    change coefficient (normalGNSRepresentation e) η ξ (e (WeakDual.toStrongDual F)) = _
    rw [hx, e.symm_apply_apply]
    rfl
  rw [heq]
  exact (WeakDual.eval_continuous x).star

lemma normalGNSWeak_injective (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Function.Injective (normalGNSWeak e) := by
  intro F G h
  have hrep := congrArg ContinuousLinearMapWOT.toCLM h
  have he := normalGNSRepresentation_injective e hrep
  have hd := e.injective he
  exact DFunLike.ext _ _ (fun x => congrArg (fun f : StrongDual ℂ X => f x) hd)

lemma normalGNSWeak_image_ball (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (C : ℝ) :
    normalGNSWeak e '' {F : WeakDual ℂ X | ‖WeakDual.toStrongDual F‖ ≤ C} =
      {A : NormalGNS e →WOT[ℂ] NormalGNS e | ∃ a : M, ‖a‖ ≤ C ∧
        ContinuousLinearMapWOT.ofCLM (normalGNSRepresentation e a) = A} := by
  ext A
  constructor
  · rintro ⟨F, hF, rfl⟩
    change ‖WeakDual.toStrongDual F‖ ≤ C at hF
    exact ⟨e (WeakDual.toStrongDual F), by simpa only [e.norm_map] using hF, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨StrongDual.toWeakDual (e.symm a), ?_, ?_⟩
    · change ‖e.symm a‖ ≤ C
      simpa only [e.symm.norm_map] using ha
    · change ContinuousLinearMapWOT.ofCLM
        (normalGNSRepresentation e (e (e.symm a))) = _
      rw [e.apply_symm_apply]

/-- Norm balls of the represented algebra are weak-operator compact. -/
theorem normalGNSWeak_ball_isCompact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (C : ℝ) :
    IsCompact {A : NormalGNS e →WOT[ℂ] NormalGNS e | ∃ a : M, ‖a‖ ≤ C ∧
      ContinuousLinearMapWOT.ofCLM (normalGNSRepresentation e a) = A} := by
  rw [← normalGNSWeak_image_ball]
  have heq : {F : WeakDual ℂ X | ‖WeakDual.toStrongDual F‖ ≤ C} =
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) C := by
    ext F
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  rw [heq]
  exact (WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) C).image (normalGNSWeak_continuous e)

/-- A bounded weak-operator limit in this representation still belongs to the
original algebra with the same bound. -/
theorem normalGNSWeak_ball_isClosed (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (C : ℝ) :
    IsClosed {A : NormalGNS e →WOT[ℂ] NormalGNS e | ∃ a : M, ‖a‖ ≤ C ∧
      ContinuousLinearMapWOT.ofCLM (normalGNSRepresentation e a) = A} :=
  (normalGNSWeak_ball_isCompact e C).isClosed

end BoundedHochschild.KadisonRingrose

end

end OAI
