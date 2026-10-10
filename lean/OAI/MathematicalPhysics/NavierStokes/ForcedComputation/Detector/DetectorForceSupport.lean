import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorFluid
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularForce
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StartupEffective

namespace OAI

/-! Locality of the prescribed force: where the planar processor and every
injection vanish on a spatial neighborhood, all terms of the force vanish. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Filter
open scoped ContDiff Topology

theorem triangularForce_zero_of_neighborhood {a : ℝ → Plane → Plane}
    {h : ℝ → Plane → ℝ} (ha : ContDiff ℝ ∞ (Function.uncurry a))
    {U : Set Plane} (hU : IsOpen U)
    (hz : ∀ t x, x ∈ U → a t x = 0 ∧ h t x = 0)
    (ν t : ℝ) {x : Space} (hx : horizontalLinear x ∈ U) :
    triangularForce ν a h (t, x) = 0 := by
  have hn : ∀ᶠ y : SpaceTime in 𝓝 (t, x), horizontalLinear y.2 ∈ U :=
    (hU.preimage (horizontalLinear.continuous.comp continuous_snd)).mem_nhds hx
  have he : triangularVelocity a (fun _ _ => 0) =ᶠ[𝓝 (t, x)]
      (fun _ : SpaceTime => (0 : Space)) := by
    filter_upwards [hn] with y hy
    simp only [triangularVelocity, triangularLift, (hz y.1 _ hy).1,
      map_zero, zero_smul, add_zero]
  rw [triangularForce_eq_residual ha]
  change residual ν (triangularVelocity a (fun _ _ => 0)) (t, x) +
    triangularVelocity (fun _ _ => 0) h (t, x) = 0
  rw [residual_congr_germ he ν, residual_eq_force_add]
  simp only [Pi.add_apply]
  rw [force_eq_mixed contDiff_const, convectiveField_eq_mixed contDiff_const]
  simp only [mixedDerivative_zero, Finset.sum_const_zero, smul_zero,
    sub_zero, add_zero, triangularVelocity, triangularLift, map_zero,
    (hz t _ hx).2, zero_smul]

theorem detector_coefficients_zero_of_neighborhood {V : ℝ → Plane → Plane}
    (C L : ℕ) {U : Set Plane}
    (hV : ∀ s x, x ∈ U → V s x = 0)
    (hb : ∀ n x, x ∈ U → detectorBump (width L n : ℝ) x = 0)
    (t : ℝ) {x : Plane} (hx : x ∈ U) :
    detectorDrift V C L t x = 0 ∧ detectorSource C L t x = 0 := by
  constructor
  · change (∑' n, detectorDriftTerm V C L n (t, x)) = 0
    have he (n : ℕ) : detectorDriftTerm V C L n (t, x) = 0 := by
      simp only [detectorDriftTerm, hV _ x hx, smul_zero]
    simp only [he, tsum_zero]
  · change (∑' n, detectorSourceTerm C L n (t, x)) = 0
    have he (n : ℕ) : detectorSourceTerm C L n (t, x) = 0 := by
      simp only [detectorSourceTerm, hb n x hx, mul_zero]
    simp only [he, tsum_zero]

theorem detectorForce_zero_of_neighborhood {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (C L : ℕ)
    {U : Set Plane} (hU : IsOpen U)
    (hVz : ∀ s x, x ∈ U → V s x = 0)
    (hb : ∀ n x, x ∈ U → detectorBump (width L n : ℝ) x = 0)
    (t : ℝ) {x : Space} (hx : horizontalLinear x ∈ U) :
    detectorForce V C L (t, x) = 0 :=
  triangularForce_zero_of_neighborhood (detectorDrift_smooth hV C L) hU
    (fun s _ hy => detector_coefficients_zero_of_neighborhood C L hVz hb s hy) 1 t hx

end ForcedComputation.VelocityDetector

end

end OAI
