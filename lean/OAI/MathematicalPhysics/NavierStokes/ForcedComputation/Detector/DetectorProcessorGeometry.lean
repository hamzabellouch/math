import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarProcessorMain
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TorusGeometry

namespace OAI

/-! The planar processor's full nonhalting corridor supplies the detector's
torus clearance, including across the boundary of a fundamental square. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set

theorem vertical_corridor_torus_separation {p x : Plane}
    (hp₀ : (3 / 16 : ℝ) ≤ p 1) (hp₁ : p 1 ≤ (7 / 8 : ℝ))
    (hx₀ : (1 / 32 : ℝ) < x 1) (hx₁ : x 1 < (1 / 8 : ℝ)) :
    1 / 16 ≤ torusNorm (p - x) := by
  let r := p 1 - x 1
  have hlo : (1 / 16 : ℝ) ≤ r := by dsimp only [r]; linarith
  have hhi : r ≤ (27 / 32 : ℝ) := by dsimp only [r]; linarith
  have habs : (1 / 16 : ℝ) ≤ |r - (⌊r + 1 / 2⌋ : ℤ)| := by
    by_cases hr : r + 1 / 2 < 1
    · have hf : ⌊r + 1 / 2⌋ = (0 : ℤ) := Int.floor_eq_iff.mpr ⟨by linarith, by simpa using hr⟩
      rw [hf, Int.cast_zero, sub_zero, abs_of_nonneg (by linarith)]
      exact hlo
    · have hf : ⌊r + 1 / 2⌋ = (1 : ℤ) :=
        Int.floor_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
      rw [hf, Int.cast_one, abs_of_nonpos (by linarith)]
      linarith
  calc
    _ ≤ |centeredRepresentative (p - x) 1| := habs
    _ ≤ torusNorm (p - x) := by
      simpa only [torusNorm, Real.norm_eq_abs, planeCoordinates,
        PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_toLp] using
        PiLp.norm_apply_le (planeCoordinates.symm (centeredRepresentative (p - x))) (1 : Fin 2)

theorem processor_nonhalting_clearance
    (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {Ω Ψ : ℝ → ℝ → Plane → Plane}
    (h : Recorder.Planar.ProcessorProperties I hI Ω Ψ)
    (hno : ¬ Alternating.Halts I) (s : ℝ) (hs : 0 ≤ s)
    (x : Plane) (hx : x ∈ Recorder.Planar.observer) :
    1 / 16 ≤ torusNorm (Ω 0 s ![1 / 4, 1 / 4] - x) := by
  have hc := (h.nonhalting hno s hs).1
  have hhi := (hc.1 1).2
  norm_num [clockRectangle] at hhi
  exact vertical_corridor_torus_separation hc.2 hhi hx.1 hx.2

end ForcedComputation.VelocityDetector

end

end OAI
