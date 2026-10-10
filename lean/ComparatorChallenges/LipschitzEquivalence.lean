import Mathlib

namespace OAI

universe uE uF

noncomputable section
namespace LipschitzCounterexample

abbrev RealL2 := lp (fun _ : ℕ => ℝ) 2
abbrev C0L2 := ZeroAtInftyContinuousMap ℕ RealL2

structure SeparableRealBanach where
  Carrier : Type
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [normedSpace : NormedSpace ℝ Carrier]
  [completeSpace : CompleteSpace Carrier]
  [separableSpace : TopologicalSpace.SeparableSpace Carrier]

attribute [instance] SeparableRealBanach.normedAddCommGroup
  SeparableRealBanach.normedSpace SeparableRealBanach.completeSpace
  SeparableRealBanach.separableSpace

def ContainsLinearCopy (E : Type uE) (F : Type uF) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∃ (T : E →L[ℝ] F) (a : ℝ), 0 < a ∧ ∀ x : E, a * ‖x‖ ≤ ‖T x‖

def MainClaim : Prop :=
  ∃ X Y : SeparableRealBanach,
    ∃ Ψ : X.Carrier ≃ Y.Carrier,
      (∀ s t : X.Carrier,
        (4 / 21 : ℝ) * ‖s - t‖ ≤ ‖Ψ s - Ψ t‖ ∧
        ‖Ψ s - Ψ t‖ ≤ (76 / 25 : ℝ) * ‖s - t‖) ∧
      IsEmpty (X.Carrier ≃L[ℝ] Y.Carrier) ∧
      Nonempty (C0L2 →ₗᵢ[ℝ] X.Carrier) ∧
      ¬ ContainsLinearCopy C0L2 Y.Carrier

theorem main : MainClaim := by
  sorry

end LipschitzCounterexample
end

end OAI
