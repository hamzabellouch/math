import OAI.Analysis.LipschitzHilbert.Trees.SourceSnapshotSize
import OAI.Analysis.LipschitzHilbert.Phase.SourcePhaseParameters

namespace OAI

/-! The actual concentration bound n <= N L^C supplies the amplitude
scale used in the marked prediction, with no extra mass-size premise. -/

noncomputable section
namespace LipschitzHilbert

/-- Raising the concentration mass bound to a phase in [0,1] preserves
its fixed polynomial factor and the manuscript's single power N^mu. -/
theorem source_concentration_phase_power {L N n C μ : ℝ}
    (hL : 1 ≤ L) (hN : 0 < N) (hn : 0 < n) (hC : 0 ≤ C)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hmass : n ≤ L^C*N) :
    n^μ ≤ L^C*(1+N^μ) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  calc
    _ ≤ (L^C*N)^μ := Real.rpow_le_rpow hn.le hmass hμ0
    _ = L^(C*μ)*N^μ := by
      rw [Real.mul_rpow (Real.rpow_nonneg hL0 C) hN.le,← Real.rpow_mul hL0]
    _ ≤ L^C*N^μ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hL (mul_le_of_le_one_right hC hμ1))
      (Real.rpow_nonneg hN.le μ)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hL0 C)

/-- Both mass and node-size premises of the source predictor follow with
C_* = C + Q from the concentration and actual node-amplitude bounds. -/
theorem source_snapshot_amplitude_scale {L N n C Q μ : ℝ}
    (hL : 1 ≤ L) (hN : 0 < N) (hn : 0 < n) (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hmass : n ≤ L^C*N) :
    n^μ ≤ L^(Q+C)*(1+N^μ) ∧ L^Q*n^μ ≤ L^(Q+C)*(1+N^μ) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hb := source_concentration_phase_power hL hN hn hC hμ0 hμ1 hmass
  have hproduct : L^Q*(L^C*(1+N^μ)) = L^(Q+C)*(1+N^μ) := by
    rw [← mul_assoc,← Real.rpow_add hL0]
  have hsize : L^Q*n^μ ≤ L^(Q+C)*(1+N^μ) := by
    rw [← hproduct]
    exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hL0.le Q)
  exact ⟨(le_mul_of_one_le_left (Real.rpow_nonneg hn.le μ)
    (Real.one_le_rpow hL hQ)).trans hsize,hsize⟩

end LipschitzHilbert

end

end OAI
