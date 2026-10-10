import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightSamplingPolytope

namespace OAI

/-! # A genuine coordinate ball inside the shrunken sampling domain -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {U W I : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I]

/-- Continuity at zero supplies the positive sampling radius; it is not
an extra geometric hypothesis. -/
theorem exists_small_height_sampling_ball (q : U →L[ℝ] W)
    (α : I → W →L[ℝ] ℝ) (hα : ∀ i, α i ≠ 0)
    {a : ℝ} (ha : 0 < a) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ Metric.closedBall (0 : U) R,
      q z ∈ (fun w : W => a • w) '' interior (weightSamplingPolytope α) := by
  have hz : (0 : W) ∈ interior (weightSamplingPolytope α) :=
    weightSamplingInterior_subset_interior α (zero_mem_weightSamplingInterior α hα)
  have hc : Continuous (fun z : U => a⁻¹ • q z) := continuous_const.smul q.continuous
  have hn : (fun z : U => a⁻¹ • q z) ⁻¹' interior (weightSamplingPolytope α) ∈ 𝓝 0 := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using isOpen_interior.mem_nhds hz
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r / 2, by positivity, fun z hz => ⟨a⁻¹ • q z, hsub ?_, ?_⟩⟩
  · exact (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt (by linarith)))
  · simp [smul_smul, ha.ne']

end PolycyclicRecognition

end

end OAI
