import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCylinderCalculus

namespace OAI

/-! Spatial derivatives on a closed time slab agree with ordinary
derivatives of each full-space slice, including at time zero. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open Set
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem cylinder_spatial_fderiv_eq {T : ℝ} {U : ℝ × E → F}
    (hU : ContDiffOn ℝ ∞ U (Icc 0 T ×ˢ univ))
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    fderiv ℝ (fun z => U (t, z)) x =
      (fderivWithin ℝ U (Icc 0 T ×ˢ univ) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hd := (hU.differentiableOn (by simp) (t, x) ⟨ht, mem_univ x⟩).hasFDerivWithinAt
  have hi := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
  have hc := hd.comp_hasFDerivAt x hi
    (Filter.Eventually.of_forall (fun z => ⟨ht, mem_univ z⟩))
  convert hc.fderiv using 1
  · rfl
  · ext z
    rfl

theorem cylinder_spatial_fderiv_smooth {T : ℝ} (hT : 0 < T) {U : ℝ × E → F}
    (hU : ContDiffOn ℝ ∞ U (Icc 0 T ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun y : ℝ × E => fderiv ℝ (fun z => U (y.1, z)) y.2)
      (Icc 0 T ×ˢ univ) := by
  have hS : UniqueDiffOn ℝ (Icc 0 T ×ˢ (univ : Set E)) :=
    (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hf : ContDiffOn ℝ ∞ (fderivWithin ℝ U (Icc 0 T ×ˢ univ))
      (Icc 0 T ×ˢ univ) := hU.fderivWithin hS (by simp)
  have hh := hf.clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ E))
  apply hh.congr
  rintro ⟨t, x⟩ hx
  exact cylinder_spatial_fderiv_eq hU hx.1 x

theorem cylinder_second_spatial_fderiv_smooth {T : ℝ} (hT : 0 < T)
    {U : ℝ × E → F} (hU : ContDiffOn ℝ ∞ U (Icc 0 T ×ˢ univ)) :
    ContDiffOn ℝ ∞
      (fun y : ℝ × E => fderiv ℝ (fderiv ℝ (fun z => U (y.1, z))) y.2)
      (Icc 0 T ×ˢ univ) :=
  cylinder_spatial_fderiv_smooth hT (cylinder_spatial_fderiv_smooth hT hU)

end ForcedComputation.VelocityDetector

end

end OAI
