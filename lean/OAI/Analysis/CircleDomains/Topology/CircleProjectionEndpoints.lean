import OAI.Analysis.CircleDomains.Topology.QuarterCircleSignedSubstitution
import OAI.Analysis.CircleDomains.Rigidity.AxialChordInterior

namespace OAI

/-! The endpoint maps in axial slicing are exactly the four quarter arcs. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def horizontalCirclePoint (right : Bool) (c : ℂ) (r y : ℝ) : ℂ :=
    ⟨c.re+quadrantSign right*Real.sqrt (r^2-(y-c.im)^2),y⟩
 def verticalCirclePoint (top : Bool) (c : ℂ) (r x : ℝ) : ℂ :=
    ⟨x,c.im+quadrantSign top*Real.sqrt (r^2-(x-c.re)^2)⟩

 theorem horizontalCirclePoint_quarter (c : ℂ) {r θ : ℝ} (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (0 : ℝ) (Real.pi/2)) (s t : Bool) :
    horizontalCirclePoint s c r (c.im+quadrantSign t*r*Real.sin θ) = quadrantPoint c r s t θ := by
  have he : (c.im+quadrantSign t*r*Real.sin θ-c.im)^2 = (r*Real.sin θ)^2 := by
    cases t <;> simp [quadrantSign]
  apply Complex.ext
  · simp only [horizontalCirclePoint,he,quarter_sin_sqrt hr hθ,quadrantPoint,quadrantNormal,
      Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  · simp only [horizontalCirclePoint,quadrantPoint,quadrantNormal,Complex.add_im,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    ring

 theorem verticalCirclePoint_quarter (c : ℂ) {r θ : ℝ} (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (0 : ℝ) (Real.pi/2)) (s t : Bool) :
    verticalCirclePoint t c r (c.re+quadrantSign s*r*Real.cos θ) = quadrantPoint c r s t θ := by
  have he : (c.re+quadrantSign s*r*Real.cos θ-c.re)^2 = (r*Real.cos θ)^2 := by
    cases s <;> simp [quadrantSign]
  apply Complex.ext
  · simp only [verticalCirclePoint,quadrantPoint,quadrantNormal,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  · simp only [verticalCirclePoint,he,quarter_cos_sqrt hr hθ,quadrantPoint,quadrantNormal,
      Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    ring

end CircleDomainRigidity

end

end OAI
