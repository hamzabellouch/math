import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.Radial

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped ContDiff

namespace CoulombAtom
open CoulombAnalysis

def realPacketSeed (x : Space) : ℝ := Real.smoothTransition (1-4*‖x‖^2)
lemma realPacketSeed_smooth : ContDiff ℝ ∞ realPacketSeed := by
  apply Real.smoothTransition.contDiff.comp
  exact contDiff_const.sub (contDiff_const.mul (contDiff_id.norm_sq ℝ))
lemma realPacketSeed_zero {x : Space} (hx : 1/2 ≤ ‖x‖) : realPacketSeed x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [norm_nonneg x]
lemma realPacketSeed_tsupport : tsupport realPacketSeed ⊆ closedBall (0 : Space) (1/2) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  rw [mem_closedBall,dist_zero_right]
  by_contra hh
  exact hx (realPacketSeed_zero (not_le.mp hh).le)
lemma realPacketSeed_compact : HasCompactSupport realPacketSeed :=
  (isCompact_closedBall (0:Space) (1/2)).of_isClosed_subset isClosed_closure realPacketSeed_tsupport
lemma realPacketSeed_sq_integrable : Integrable (fun x => realPacketSeed x^2) :=
  (realPacketSeed_smooth.continuous.pow 2).integrable_of_hasCompactSupport (by simpa only [pow_two] using realPacketSeed_compact.mul_left (f := realPacketSeed))
lemma realPacketSeed_mass_pos : 0 < ∫ x, realPacketSeed x^2 := by
  apply (realPacketSeed_smooth.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (by simpa only [pow_two] using realPacketSeed_compact.mul_left (f := realPacketSeed)) (fun x => sq_nonneg _ ) (x := 0)
  simp [realPacketSeed,Real.smoothTransition.one_of_one_le]

def canonicalRealPacket (x : Space) : ℝ := (Real.sqrt (∫ z, realPacketSeed z^2))⁻¹*realPacketSeed x
lemma canonicalRealPacket_smooth : ContDiff ℝ ∞ canonicalRealPacket :=
  contDiff_const.mul realPacketSeed_smooth
lemma canonicalRealPacket_compact : HasCompactSupport canonicalRealPacket :=
  realPacketSeed_compact.mul_left
lemma canonicalRealPacket_normalized : ∫ x, canonicalRealPacket x^2 = 1 := by
  simp only [canonicalRealPacket,mul_pow,integral_const_mul,inv_pow,
    Real.sq_sqrt realPacketSeed_mass_pos.le]
  exact inv_mul_cancel₀ realPacketSeed_mass_pos.ne'
lemma canonicalRealPacket_radial : IsRadial canonicalRealPacket := by
  intro x y h
  simp only [canonicalRealPacket,realPacketSeed,h]
lemma canonicalRealPacket_support : tsupport canonicalRealPacket ⊆ ball (0:Space) 1 := by
  intro x hx
  have hh : x ∈ tsupport realPacketSeed := tsupport_mul_subset_right hx
  have hn : ‖x‖ ≤ (1/2:ℝ) := by simpa only [mem_closedBall,dist_zero_right] using realPacketSeed_tsupport hh
  simp only [mem_ball,dist_zero_right]
  linarith

end CoulombAtom

end

end OAI
