import OAI.Geometry.SurfaceImmersion.Correction.SmoothParameterIntegral
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive

namespace OAI

/-! Jointly smooth normalized primitives with parameters. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem contDiff_rawPrimitive_joint {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun z : P × ℝ => rawPrimitive (fun t => F (z.1, t)) z.2) := by
  let A : (P × ℝ) × ℝ → E := fun z => F (z.1.1, z.1.2 * z.2)
  have hA : ContDiff ℝ ∞ A := hF.comp
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.mul contDiff_snd))
  have hi := SmoothParameterIntegral.contDiff_integral hA 0 1
  have hs := contDiff_snd.smul hi
  convert hs using 1
  funext z
  change (∫ t in 0..z.2, F (z.1, t)) =
    z.2 • (∫ t in 0..1, F (z.1, z.2 * t))
  simpa only [A, rawPrimitive, mul_zero, mul_one, Pi.smul_apply] using
    (intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
      (fun t => F (z.1, t)) z.2).symm

/-- Normalization by the mean preserves joint smoothness in the parameter
and the real periodic argument. -/
theorem contDiff_primitive_joint {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun z : P × ℝ => primitive (fun t => F (z.1, t)) z.2) := by
  have hraw := contDiff_rawPrimitive_joint hF
  have hmean := SmoothParameterIntegral.contDiff_integral hraw 0 1
  exact hraw.sub (hmean.comp contDiff_fst)

omit [CompleteSpace E] in
lemma primitive_zero (x : ℝ) : primitive (fun _ : ℝ => (0 : E)) x = 0 := by
  simp [primitive, rawPrimitive]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [CompleteSpace E] in
lemma primitive_zero_at_parameter {F : P × ℝ → E} {p : P}
    (hz : ∀ t, F (p, t) = 0) (x : ℝ) :
    primitive (fun t => F (p, t)) x = 0 := by
  simp only [hz]
  exact primitive_zero x

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
