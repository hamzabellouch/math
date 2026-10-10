import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularFluid

namespace OAI

/-! The detector's viscosity rescaling preserves its vertical height.
Only the planar drift is multiplied by the viscosity. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

def viscosityDrift (ν : ℝ) (a : ℝ → Plane → Plane) (t : ℝ) : Plane → Plane :=
  fun x => ν • a (ν * t) x

def viscosityScalar (ν : ℝ) (w : ℝ → Plane → ℝ) (t : ℝ) : Plane → ℝ := w (ν * t)

def viscositySource (ν : ℝ) (h : ℝ → Plane → ℝ) (t : ℝ) : Plane → ℝ :=
  fun x => ν * h (ν * t) x

theorem viscosityDrift_smooth {a : ℝ → Plane → Plane}
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (ν : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (viscosityDrift ν a)) := by
  exact (contDiff_const (c := ν)).smul
    (ha.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd))

theorem viscosityScalar_smooth {w : ℝ → Plane → ℝ}
    (hw : ContDiff ℝ ∞ (Function.uncurry w)) (ν : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (viscosityScalar ν w)) :=
  hw.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd)

theorem GlobalTorusScalarSolution.viscosity {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hs : GlobalTorusScalarSolution 1 a h w w₀)
    (hw : ContDiff ℝ ∞ (Function.uncurry w)) {ν : ℝ} (hν : 0 ≤ ν) :
    GlobalTorusScalarSolution ν (viscosityDrift ν a) (viscositySource ν h)
      (viscosityScalar ν w) w₀ := by
  intro T _
  refine ⟨(viscosityScalar_smooth hw ν).contDiffOn, ?_, ?_, ?_⟩
  · intro t ht
    have ht₀ := mul_nonneg hν ht.1
    exact (hs (ν * t) ht₀).periodic (ν * t) ⟨ht₀, le_rfl⟩
  · simpa only [viscosityScalar, mul_zero] using (hs 0 le_rfl).initial
  · intro t ht x
    have ht₀ := mul_nonneg hν ht.1
    have hd : HasDerivAt (fun r => w r x)
        (scalarGenerator 1 (a (ν * t)) (w (ν * t)) x + h (ν * t) x) (ν * t) := by
      rw [← hs.deriv_eq hw ht₀ x]
      exact ((hw.comp (contDiff_id.prodMk contDiff_const)).differentiable
        (by simp) (ν * t)).hasDerivAt
    have hc := (hd.scomp t (by simpa only [mul_one, id_eq] using
      (hasDerivAt_id t).const_mul ν)).hasDerivWithinAt (s := Icc (0 : ℝ) T)
    convert hc using 1
    · rfl
    · simp only [scalarGenerator, viscosityDrift, viscosityScalar, viscositySource,
        map_smul, smul_eq_mul, one_mul]
      ring

end ForcedComputation.VelocityDetector

end

end OAI
