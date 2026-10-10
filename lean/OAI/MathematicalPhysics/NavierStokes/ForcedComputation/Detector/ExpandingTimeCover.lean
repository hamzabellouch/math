import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingStageTimes

namespace OAI

/-! The finite stages cover every time after the initial pulse. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector

theorem exists_stage_at_time {σ D K t : ℝ} (hσ : 0 < σ) (hD : 1 ≤ D)
    (hK : 0 ≤ K) (ht : 2 ≤ t) :
    ∃ n : ℕ, stageStart σ D K n ≤ t ∧ t < stageStart σ D K (n + 1) := by
  have hex : ∃ n : ℕ, t < stageStart σ D K (n + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt t
    refine ⟨n, ?_⟩
    have hs := stageStart_ge hσ hD hK (n + 1)
    push_cast at hs
    have hz : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  let n := Nat.find hex
  refine ⟨n, ?_, Nat.find_spec hex⟩
  cases hn : n with
  | zero => simpa only [hn, stageStart_zero] using ht
  | succ k =>
    have hk : ¬ t < stageStart σ D K (k + 1) :=
      Nat.find_min hex (by omega : k < Nat.find hex)
    simpa only [hn, Nat.succ_eq_add_one] using le_of_not_gt hk

end ForcedComputation.ExpandingDetector

end

end OAI
