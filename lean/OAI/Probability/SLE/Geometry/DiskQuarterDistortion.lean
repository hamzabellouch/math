import OAI.Probability.SLE.Geometry.DiskRecentering
import OAI.Probability.SLE.Geometry.PhysicalCellDisk

namespace OAI

/-! Two-sided derivative comparison on the fixed quarter disk. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma univalent_quarter_derivative_lower (hgrowth : PublishedDiskUnivalentGrowth)
    {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hi : InjOn f (ball 0 1)) {w : ℂ} (hw : ‖w‖ ≤ 1/4) :
    ‖deriv f 0‖ / 16 ≤ ‖deriv f w‖ := by
  have hw1 : ‖w‖ < 1 := by linarith
  let g := f ∘ diskRecenter w
  have hgd : DifferentiableOn ℂ g (ball 0 1) :=
    hd.comp (diskRecenter_differentiable hw1) (diskRecenter_maps hw1)
  have hgi : InjOn g (ball 0 1) := hi.comp (diskRecenter_injOn hw1) (diskRecenter_maps hw1)
  have hnorm (z : ℂ) (hz : z ∈ ball 0 1) :
      ‖deriv g z‖ = ‖deriv f (diskRecenter w z)‖ * ‖deriv (diskRecenter w) z‖ := by
    have hf := hd.differentiableAt (isOpen_ball.mem_nhds (diskRecenter_maps hw1 hz))
    have hg := (diskRecenter_hasDerivAt hw1 (mem_ball_zero_iff.mp hz)).differentiableAt
    change ‖deriv (f ∘ diskRecenter w) z‖ = _
    rw [deriv_comp z hf hg,norm_mul]
  have hzero := hnorm 0 (mem_ball_self (by norm_num : (0:ℝ)<1))
  simp only [diskRecenter_zero,diskRecenter_deriv_zero hw1] at hzero
  have hneg := hnorm (-w) (mem_ball_zero_iff.mpr (by simpa only [norm_neg] using hw1))
  simp only [diskRecenter_neg,diskRecenter_deriv_neg hw1] at hneg
  have hh := univalent_quarter_derivative_upper hgrowth hgd hgi
    (show ‖-w‖ ≤ 1/4 by simpa only [norm_neg] using hw)
  rw [hzero,hneg] at hh
  let δ : ℝ := 1-‖w‖^2
  have hδ : 0 < δ := (diskRecenter_det hw1).2
  have hδ1 : δ ≤ 1 := by dsimp [δ]; nlinarith [sq_nonneg ‖w‖]
  change ‖deriv f 0‖ * δ⁻¹ ≤ 16 * (‖deriv f w‖ * δ) at hh
  have hbound : ‖deriv f 0‖ ≤ 16*‖deriv f w‖*δ^2 := by
    calc
      _ = (‖deriv f 0‖*δ⁻¹)*δ := by field_simp
      _ ≤ (16*(‖deriv f w‖*δ))*δ := mul_le_mul_of_nonneg_right hh hδ.le
      _ = _ := by ring
  have hsq : δ^2 ≤ 1 := by nlinarith
  have hlast := hbound.trans (mul_le_of_le_one_right
    (mul_nonneg (by norm_num : (0:ℝ)≤16) (norm_nonneg _)) hsq)
  linarith

lemma univalent_quarter_derivative_bounds (hgrowth : PublishedDiskUnivalentGrowth)
    {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hi : InjOn f (ball 0 1)) {w : ℂ} (hw : ‖w‖ ≤ 1/4) :
    ‖deriv f 0‖ / 16 ≤ ‖deriv f w‖ ∧ ‖deriv f w‖ ≤ 16*‖deriv f 0‖ :=
  ⟨univalent_quarter_derivative_lower hgrowth hd hi hw,
    univalent_quarter_derivative_upper hgrowth hd hi hw⟩

lemma IsCapacityTwoWitness.quarter_disk_derivative_bounds
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hgrowth : PublishedDiskUnivalentGrowth)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (w : ℂ) (hw' : w ∈ closedBall 0 (1/4)) :
    fullRadius G t z / 16 ≤ ‖deriv (physicalDiskChart id F G t z) w‖ ∧
      ‖deriv (physicalDiskChart id F G t z) w‖ ≤ 16*fullRadius G t z := by
  obtain ⟨hd,hi,_,hder,_⟩ := hw.physical_disk_chart id differentiableOn_id
    (fun _ _ _ _ h => h) t z hz
  have hr : ‖deriv (physicalDiskChart id F G t z) 0‖ = fullRadius G t z := by
    simpa [physicalConformalRadius] using hder
  have hn : ‖w‖ ≤ 1/4 := by simpa only [mem_closedBall,dist_zero_right] using hw'
  simpa only [hr] using univalent_quarter_derivative_bounds hgrowth hd hi hn

end SLEExactGauge

end

end OAI
