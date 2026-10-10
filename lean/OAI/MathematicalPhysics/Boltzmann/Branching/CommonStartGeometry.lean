import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricCommonBlock

namespace OAI

section

/-! # The common finite block written at an arbitrary characteristic starting phase -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightCharacteristic_from_phase (s Δ : ℝ) (p : WeakTime.Phase) :
    flightCharacteristicEquiv (s+Δ) (Δ,flight s p) = (s,p) := by
  change (s+Δ-Δ,((p.1+s • p.2)-(s+Δ-Δ) • p.2,p.2)) = (s,p)
  simp only [add_sub_cancel_right,add_sub_cancel_right]

theorem lateBox_retained_velocity {κ d s : ℝ} {p : WeakTime.Phase}
    (hp : flight s p ∈ lateBox κ d s) : p.2 ∈ referenceRegion := by
  simpa only [referenceRegion,Metric.mem_closedBall,dist_zero_right,flight] using hp.2.le

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Starting phases and the spatial cutoff on a common late-box window -/

noncomputable section
open Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lateBox_start_commonCore {κ d b W s : ℝ}
    (hκ : 0 < κ) (hκsmall : κ ≤ 1) (hd : d ≤ 1/32) (hb : 0 < b)
    (hW : W ≤ κ*b/200) (hs : s ∈ Icc b (b+W))
    {p : WeakTime.Phase} (hp : flight s p ∈ lateBox κ d s) :
    (s,p) ∈ characteristicHistoryCore b (κ*b/4) ((κ*b) • firstAxis) := by
  have hv : ‖p.2‖ ≤ 6 := hp.2.le.trans (by norm_num)
  have hzero : (0:ℝ) ≤ W := by linarith [hs.1,hs.2]
  have hc := boundedFlightCone_mem_commonCore (s := s) (Δ := 0)
    hκ hκsmall hd hb hW hs hzero hp (boundedFlightCone_refl (by norm_num) hv)
  rw [show flightCharacteristicEquiv (s+0) (0,p.1+s • p.2,p.2) = (s,p) from
    flightCharacteristic_from_phase s 0 p] at hc
  exact hc

theorem lateBox_above_spatial_cutoff {κ d b W s Δ L : ℝ}
    (hκ : 0 < κ) (hd : d ≤ 1/32) (hb : 0 < b) (hs : b ≤ s) (hΔ : Δ ≤ W)
    (hcut : L+6*W < κ*b/2) {p : V × V} (hp : p ∈ lateBox κ d s) :
    L+6*Δ < ‖transverse p.1‖ := by
  have hspos := hb.trans_le hs
  have hh := (lateBox_radius_bounds hκ hspos hp).1
  have hd' := mul_le_mul_of_nonneg_right hd (mul_pos hκ hspos).le
  have hb' := mul_le_mul_of_nonneg_left hs hκ.le
  nlinarith

theorem phase_block_lower {κ d s Δ : ℝ} (H : (ℝ × WeakTime.Phase) → ℝ≥0∞) (g : ℝ≥0∞)
    (hphysical : ∀ (x : V) (v : RetainedState), (x,(v:V)) ∈ lateBox κ d s →
      g ≤ H (flightCharacteristicEquiv (s+Δ) (Δ,(x,(v:V))))) :
    ∀ p ∈ flight s ⁻¹' lateBox κ d s, g ≤ H (s,p) := by
  intro p hp
  let v : RetainedState := ⟨p.2,lateBox_retained_velocity (κ := κ) (d := d) (s := s) (p := p) hp⟩
  have hh := hphysical (flight s p).1 v hp
  change g ≤ H (flightCharacteristicEquiv (s+Δ) (Δ,p.1+s • p.2,p.2)) at hh
  rw [show flightCharacteristicEquiv (s+Δ) (Δ,p.1+s • p.2,p.2) = (s,p) from
    flightCharacteristic_from_phase s Δ p] at hh
  exact hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
