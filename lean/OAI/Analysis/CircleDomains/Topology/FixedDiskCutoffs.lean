import OAI.Analysis.CircleDomains.Sobolev.SmoothContours
import OAI.Analysis.CircleDomains.Sobolev.ComplexWeakGradient

namespace OAI

/-! Fixed source and target cutoffs are chosen before the near-extremal
model, so their derivative constants do not depend on that model. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem exists_complex_disk_cutoff {r R : ℝ} (hrR : r < R) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ ball 0 R ∧ (∀ z, f z ∈ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ closedBall 0 r, f z = 1) := by
  obtain ⟨f,hf,hs,hsub,hu,hf1⟩ := exists_smooth_planar_cutoff
    (isCompact_closedBall (0 : ℂ) r) isOpen_ball (closedBall_subset_ball hrR)
  exact ⟨f,hf,hs,hsub,hu,fun z hz => hf1.self_of_nhdsSet z hz⟩

 theorem exists_physical_disk_cutoff {r R : ℝ} (hrR : r < R) :
    ∃ (f : EuclideanPlane → ℝ) (C : ℝ), 0 ≤ C ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ ball 0 R ∧
      (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧ (∀ x ∈ closedBall 0 r, f x = 1) ∧
      (∀ x, ‖fderiv ℝ f x‖ ≤ C) := by
  obtain ⟨g,hg,hgs,hgsub,hgu,hg1⟩ := exists_complex_disk_cutoff hrR
  let f := g ∘ complexPlaneCoordinates
  have hf : ContDiff ℝ ∞ f := hg.comp complexPlaneCoordinates.contDiff
  have hs : HasCompactSupport f := hgs.comp_homeomorph complexPlaneCoordinates.toHomeomorph
  obtain ⟨C,hC⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  refine ⟨f,max C 0,le_max_right _ _,hf,hs,?_,fun x => hgu _,?_,
    fun x => (hC x).trans (le_max_left _ _)⟩
  · rw [show f = g ∘ complexPlaneCoordinates.toHomeomorph from rfl, tsupport_comp_eq_preimage]
    intro x hx
    have hz := hgsub hx
    change complexPlaneCoordinates x ∈ ball (0 : ℂ) R at hz
    simpa only [mem_ball, dist_zero_right, complexPlaneCoordinates_norm] using hz
  · intro x hx
    apply hg1
    simpa only [mem_closedBall, dist_zero_right, complexPlaneCoordinates_norm] using hx

end CircleDomainRigidity

end

end OAI
