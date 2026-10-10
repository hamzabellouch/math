import OAI.Analysis.LienardCycles.BaseLimits

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.QuadraticCoordinates

theorem R_pos {d k r : ℝ} (hr : 0 < r) : 0 < R ((d,k),r) := by
  obtain ⟨z,hz⟩ := ReferenceCharacteristic.J_surjective d k hr
  have hu := ReferenceCharacteristic.U_pos (z := z) (k := k) hr
  dsimp only [ReferenceCharacteristic.U] at hu
  rw [ReferenceCharacteristic.Dz_formula hr,hz] at hu
  have hm := (div_pos_iff_of_pos_right (ReferenceCharacteristic.D_gap_pos (q := ((z,k),r)) hr)).mp hu
  exact (mul_pos_iff_of_pos_right (ReferenceCharacteristic.Jz_pos (z := z) (k := k) hr)).mp hm

theorem G_pos {d k r : ℝ} (hr : 0 < r) : 0 < G ((d,k),r) := by
  obtain ⟨z,hz⟩ := ReferenceCharacteristic.J_surjective d k hr
  have hb := ReferenceCharacteristic.B_pos (z := z) (k := k) hr
  rw [ReferenceCharacteristic.B_formula hr,hz] at hb
  exact (div_pos_iff_of_pos_right (mul_pos (QuadraticVariation.P_pos hr)
    (ReferenceCharacteristic.D_gap_pos (q := ((z,k),r)) hr))).mp hb

theorem S_pos {d k r : ℝ} (hr : 0 < r) : 0 < S ((d,k),r) := by
  have hg := G_pos (d := d) (k := k) hr
  have hqr := mul_pos (QuadraticVariation.Q_pos (d := d) (k := k) hr) (R_pos (d := d) (k := k) hr)
  have hp := QuadraticVariation.P_pos (d := d) (k := k) hr
  dsimp [G] at hg
  exact pos_of_mul_pos_right (by linarith : 0 < P ((d,k),r)*S ((d,k),r)) hp.le

end QuinticLienard.QuadraticCoordinates

end OAI
