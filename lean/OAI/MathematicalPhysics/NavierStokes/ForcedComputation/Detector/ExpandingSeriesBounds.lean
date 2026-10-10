import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingDrift

namespace OAI

/-! Summing the geometric derivative budget of the prescribed stages.
Local finiteness lets the estimate apply to every derivative of the actual
infinite-time field. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Set Filter
open scoped ContDiff BigOperators Topology

theorem half_geometric_sum_le_two (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) ≤ 2 := by
  have he : (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) = 2 * (1 - (1 / 2 : ℝ) ^ N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [he]
  linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N]

theorem expandingDrift_jet_bound
    (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {σ D K : ℝ} (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (k : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ n y, ‖iteratedFDeriv ℝ k
      (Function.uncurry (stageDrift M hM blank m σ D K n)) y‖ ≤ B * (1 / 2 : ℝ) ^ n)
    (y : ℝ × Plane) :
    ‖iteratedFDeriv ℝ k (Function.uncurry (expandingDrift M hM blank m σ D K)) y‖ ≤ 2 * B := by
  let F := fun n => Function.uncurry (stageDrift M hM blank m σ D K n)
  have hbefore (n : ℕ) (z : ℝ × Plane) (hz : z.1 < 2 * ((n : ℝ) + 1)) : F n z = 0 :=
    stageDrift_zero_before M hM blank m hσ hD hK n
      (hz.le.trans (stageStart_ge hσ hD hK n)) z.2
  obtain ⟨N, hN⟩ := detectorBlockSum_local F hbefore y
  change ‖iteratedFDeriv ℝ k (detectorBlockSum F) y‖ ≤ 2 * B
  rw [(hN.iteratedFDeriv ℝ k).self_of_nhds,
    iteratedFDeriv_fun_sum_apply (fun n _ =>
      ((stageDrift_smooth M hM blank m σ D K n).of_le (by simp)).contDiffAt)]
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖iteratedFDeriv ℝ k (F n) y‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, B * (1 / 2 : ℝ) ^ n :=
      Finset.sum_le_sum (fun n _ => hb n y)
    _ = B * ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n := by rw [Finset.mul_sum]
    _ ≤ B * 2 := mul_le_mul_of_nonneg_left (half_geometric_sum_le_two N) hB
    _ = _ := mul_comm _ _

end ForcedComputation.ExpandingDetector

end

end OAI
