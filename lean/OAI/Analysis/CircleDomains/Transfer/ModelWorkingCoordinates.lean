import OAI.Analysis.CircleDomains.Sobolev.ComplexLocalScalarWitness
import OAI.Analysis.CircleDomains.Sobolev.ModelScalarEnergy

namespace OAI

/-! The actual normalized model coordinates have local source Sobolev
witnesses on each bounded working region. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem working_coordinate_memLp (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (R : ℝ) :
    MemLp (fun z => (M.function z).re) 2
      (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R)) ∧
    MemLp (fun z => (M.function z).im) 2
      (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R)) := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  let U := D ∩ ball (0 : ℂ) R
  have hU : IsOpen U := (hG.preimage OnePoint.continuous_coe).inter isOpen_ball
  let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    ((measure_mono (inter_subset_right : U ⊆ ball 0 R)).trans_lt measure_ball_lt_top).ne
  have hf : ContinuousOn M.function U :=
    (show DifferentiableOn ℂ M.function D from fun z hz =>
      (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt).continuousOn.mono inter_subset_left
  obtain ⟨K,_,hK⟩ := M.function_bounded_on_source_ball hinf R
  constructor
  · exact MemLp.of_bound ((Complex.continuous_re.comp_continuousOn hf).aestronglyMeasurable hU.measurableSet) K
      ((ae_restrict_mem hU.measurableSet).mono (fun z hz =>
        (Complex.abs_re_le_norm (M.function z)).trans (hK z hz.1 hz.2)))
  · exact MemLp.of_bound ((Complex.continuous_im.comp_continuousOn hf).aestronglyMeasurable hU.measurableSet) K
      ((ae_restrict_mem hU.measurableSet).mono (fun z hz =>
        (Complex.abs_im_le_norm (M.function z)).trans (hK z hz.1 hz.2)))

 theorem working_coordinate_witnesses (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (R : ℝ) :
    Nonempty (DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 R)) ∧
    Nonempty (DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 R)) := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hf : ContDiffOn ℝ ∞ M.function D :=
    ((show DifferentiableOn ℂ M.function D from fun z hz =>
      (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt).contDiffOn hD).restrict_scalars ℝ
  have he : complexPlaneCoordinates ⁻¹' (D ∩ ball 0 R) = physicalPlaneDomain G ∩ ball 0 R := by
    ext x
    simp only [mem_preimage, mem_inter_iff, D, mem_ofPred_eq, mem_ball, dist_zero_right,
      complexPlaneCoordinates_norm]
    rfl
  obtain ⟨hLr,hLi⟩ := M.working_coordinate_memLp hG hinf R
  obtain ⟨hEr,hEi⟩ := M.source_coordinate_memLp hG hinf R
  have Wr := complexLocalScalarWitness (hD.inter isOpen_ball)
    ((Complex.reCLM.contDiff.comp_contDiffOn hf).mono inter_subset_left) hLr hEr
  have Wi := complexLocalScalarWitness (hD.inter isOpen_ball)
    ((Complex.imCLM.contDiff.comp_contDiffOn hf).mono inter_subset_left) hLi hEi
  rw [he] at Wr Wi
  exact ⟨⟨Wr⟩,⟨Wi⟩⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
