import OAI.Probability.SLE.KernelConsistency
import Mathlib.Analysis.Complex.Schwarz

namespace OAI

/-! The half-plane Schwarz–Pick inequality in the form needed to compare
hydrodynamically normalized slit maps. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma halfPlane_schwarz_pick {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlane) (hm : MapsTo f upperHalfPlane upperHalfPlane)
    {z w : ℂ} (hz : z ∈ upperHalfPlane) (hw : w ∈ upperHalfPlane) :
    ‖halfPlaneToDisk (f w) (f z)‖ ≤ ‖halfPlaneToDisk w z‖ := by
  let g := halfPlaneToDisk (f w) ∘ f ∘ diskToHalfPlane w
  have hg : DifferentiableOn ℂ g (ball 0 1) :=
    (halfPlaneToDisk_differentiable (hm hw)).comp
      (hf.comp (diskToHalfPlane_differentiable w) (diskToHalfPlane_maps hw))
      (hm.comp (diskToHalfPlane_maps hw))
  have hgm : MapsTo g (ball 0 1) (closedBall 0 1) :=
    ((halfPlaneToDisk_maps (hm hw)).comp (hm.comp (diskToHalfPlane_maps hw))).mono_right
      ball_subset_closedBall
  have hg0 : g 0=0 := by simp [g,halfPlaneToDisk]
  have hh := Complex.norm_le_norm_of_mapsTo_ball hg hgm hg0
    (mem_ball_zero_iff.mp (halfPlaneToDisk_maps hw hz))
  simpa only [g,Function.comp_apply,diskToHalfPlane_halfPlaneToDisk hw hz] using hh

lemma halfPlane_normSq_difference (z w : ℂ) :
    normSq (z-conj w)-normSq (z-w)=4*z.im*w.im := by
  simp only [normSq_apply,sub_re,sub_im,conj_re,conj_im]
  ring

lemma halfPlane_schwarz_pick_kernel {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlane) (hm : MapsTo f upperHalfPlane upperHalfPlane)
    {z w : ℂ} (hz : z ∈ upperHalfPlane) (hw : w ∈ upperHalfPlane) :
    z.im*w.im*normSq (f z-conj (f w)) ≤
      (f z).im*(f w).im*normSq (z-conj w) := by
  have h := halfPlane_schwarz_pick hf hm hz hw
  have hd : 0 < normSq (z-conj w) :=
    normSq_pos.mpr (halfPlane_denominator_ne hw hz)
  have hdf : 0 < normSq (f z-conj (f w)) :=
    normSq_pos.mpr (halfPlane_denominator_ne (hm hw) (hm hz))
  have hsq : normSq (halfPlaneToDisk (f w) (f z)) ≤
      normSq (halfPlaneToDisk w z) := by
    rw [normSq_eq_norm_sq,normSq_eq_norm_sq]
    nlinarith [norm_nonneg (halfPlaneToDisk (f w) (f z)),norm_nonneg (halfPlaneToDisk w z)]
  simp only [halfPlaneToDisk,star_def,normSq_div] at hsq
  have he := (div_le_div_iff₀ hdf hd).mp hsq
  have h1 := halfPlane_normSq_difference z w
  have h2 := halfPlane_normSq_difference (f z) (f w)
  nlinarith

end SLEExactGauge

end

end OAI
