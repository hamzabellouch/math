import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateMotion

namespace OAI

/-! Every scheduled gate vanishes on time collars at both ends of its
stage. Consecutive finite arrays therefore join smoothly. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Set Filter
open scoped Topology

theorem scheduledCenter_before (a : ℝ) {T : ℝ} (hT : 0 < T)
    (S S' : ℝ) (k target : ℕ) (terminal : Bool) {t : ℝ} (ht : t ≤ a + T / 12) :
    scheduledCenter a T S S' k target terminal t = ![S * k, -S] := by
  have h₁ : firstWeight a T t = 0 := smoothRamp_before (by linarith) ht
  have h₂ : secondWeight a T t = 0 := smoothRamp_before (by linarith) (by linarith)
  have h₃ : thirdWeight a T t = 0 := smoothRamp_before (by linarith) (by linarith)
  rw [scheduledCenter, h₁, h₂, h₃, gateCenter_initial]

theorem scheduledCenter_after (a : ℝ) {T : ℝ} (hT : 0 < T)
    (S S' : ℝ) (k target : ℕ) (terminal : Bool) {t : ℝ} (ht : a + 11 * T / 12 ≤ t) :
    scheduledCenter a T S S' k target terminal t =
      ![S' * target, if terminal then S' else -S'] := by
  have h₁ : firstWeight a T t = 1 := smoothRamp_after (by linarith) (by linarith)
  have h₂ : secondWeight a T t = 1 := smoothRamp_after (by linarith) (by linarith)
  have h₃ : thirdWeight a T t = 1 := smoothRamp_after (by linarith) ht
  rw [scheduledCenter, h₁, h₂, h₃, gateCenter_final]

theorem scheduledGate_zero_before (R a : ℝ) {T : ℝ} (hT : 0 < T)
    (S S' : ℝ) (k target : ℕ) (terminal : Bool) {t : ℝ} (ht : t ≤ a) (x : Plane) :
    movingGate R (scheduledCenter a T S S' k target terminal) t x = 0 := by
  apply movingGate_zero_of_constant_near R (p := ![S * k, -S])
  have hn : Iio (a + T / 12) ∈ 𝓝 t := Iio_mem_nhds (by linarith)
  filter_upwards [hn] with s hs
  exact scheduledCenter_before a hT S S' k target terminal hs.le

theorem scheduledGate_zero_after (R a : ℝ) {T : ℝ} (hT : 0 < T)
    (S S' : ℝ) (k target : ℕ) (terminal : Bool) {t : ℝ} (ht : a + T ≤ t) (x : Plane) :
    movingGate R (scheduledCenter a T S S' k target terminal) t x = 0 := by
  apply movingGate_zero_of_constant_near R
    (p := ![S' * target, if terminal then S' else -S'])
  have hn : Ioi (a + 11 * T / 12) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  filter_upwards [hn] with s hs
  exact scheduledCenter_after a hT S S' k target terminal hs.le

end ForcedComputation.ExpandingDetector

end

end OAI
