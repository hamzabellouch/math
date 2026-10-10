import OAI.Geometry.SurfaceImmersion.Geometry.LocalParameterIntegral
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPeriodicPrimitive

namespace OAI

/-! Smooth normalized primitives on the open admissible parameter domain. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

universe u

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The primitive is jointly smooth wherever the parameter family is smooth. -/
theorem contDiffOn_primitive_joint {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => primitive (fun t => F (z.1, t)) z.2) (S ×ˢ univ) := by
  apply (hS.prod isOpen_univ).contDiffOn_iff.mpr
  intro z hz
  obtain ⟨G, hG, he⟩ := SmoothParameterIntegral.exists_smooth_extension_near hS hF hz.1
  apply (contDiff_primitive_joint hG).contDiffAt.congr_of_eventuallyEq
  have he' := (continuous_fst.continuousAt :
    Tendsto Prod.fst (𝓝 z) (𝓝 z.1)).eventually he
  filter_upwards [he'] with w hw
  have hf : (fun t => F (w.1, t)) = fun t => G (w.1, t) := funext (fun t => (hw t).symm)
  rw [hf]

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
