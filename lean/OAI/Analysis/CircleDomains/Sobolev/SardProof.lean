import OAI.Analysis.CircleDomains.Sobolev.SmoothContours
import OAI.Geometry.StableBernstein.Estimates.PuncturedSard

namespace OAI

/-! The planar scalar Sard theorem follows from finite-dimensional
scalar Sard. Only the dimension-two specialization is used here. -/
open Set MeasureTheory
open scoped ContDiff
namespace CircleDomainRigidity

/-- Smooth planar scalar functions have null critical-value sets. -/
theorem smoothPlanarSard : SmoothPlanarSard := by
  intro f hf _
  have h := Bernstein.Sard.scalar_sard_finrank_le_six (E := ℂ)
    (by rw [Complex.finrank_real_complex]; norm_num) univ isOpen_univ f hf.contDiffOn
  simpa only [mem_univ, true_and] using h

end CircleDomainRigidity

end OAI
