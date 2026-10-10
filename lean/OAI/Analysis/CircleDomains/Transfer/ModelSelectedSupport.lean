import OAI.Analysis.CircleDomains.Sobolev.ModelWorkingGradients
import OAI.Analysis.CircleDomains.Transfer.ModelFlattenedSelection

namespace OAI

/-! The actual selected support has small energy for the entire reference
map, by conformality and the retained horizontal support budget. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem selected_support_error (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d A L δ ε : ℝ} (H : ControlledHeight R d)
    {W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H W A L δ ε)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L)) :
    (eLpNorm ((complexPlaneCoordinates ⁻¹' ⋃ n, support (S.cutoff n)).indicator
      (fun x => ‖weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)‖)) 2
        (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal < 2*ε := by
  let C := ⋃ n, support (S.cutoff n)
  have hC : MeasurableSet C := MeasurableSet.iUnion
    (fun n => (S.cutoff_smooth n).continuous.isOpen_support.measurableSet)
  have hCp : MeasurableSet (complexPlaneCoordinates ⁻¹' C) :=
    hC.preimage complexPlaneCoordinates.continuous.measurable
  have hb := weak_pair_indicator_bound hCp Wx.weakGrad_memLp Wy.weakGrad_memLp
    (M.working_rows_norm_eq hG hinf L Wx Wy)
  have he : eLpNorm ((complexPlaneCoordinates ⁻¹' C).indicator (fun x => ‖Wx.weakGrad x‖)) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L)) =
      eLpNorm (C.indicator (fun z => ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z‖)) 2
        (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L)) := by
    have hn := M.working_horizontal_norm hG hinf L Wx
    have hind : (complexPlaneCoordinates ⁻¹' C).indicator (fun x => ‖Wx.weakGrad x‖) =ᵐ[
        volume.restrict (physicalPlaneDomain G ∩ ball 0 L)]
        (C.indicator (fun z => ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z‖)) ∘
          complexPlaneCoordinates := by
      filter_upwards [hn] with x hx
      by_cases hc : complexPlaneCoordinates x ∈ C
      · simpa only [indicator_of_mem hc, indicator_of_mem (show x ∈ complexPlaneCoordinates ⁻¹' C from hc), Function.comp_apply] using hx
      · simp only [Function.comp_apply, indicator_of_notMem hc,
          indicator_of_notMem (show x ∉ complexPlaneCoordinates ⁻¹' C from hc)]
    rw [eLpNorm_congr_ae hind]
    have hD := (hG.preimage OnePoint.continuous_coe).inter (isOpen_ball (x := (0 : ℂ)) (ε := L))
    have hp : complexPlaneCoordinates ⁻¹' ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L) =
        physicalPlaneDomain G ∩ ball 0 L := by
      ext x
      simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_ball, dist_zero_right,
        complexPlaneCoordinates_norm]
      rfl
    have hm := (M.horizontalSection_plane_memLp hG hinf L).norm.indicator hC
    have hh := eLpNorm_comp_measurePreserving hm.aestronglyMeasurable
      (complexPlaneCoordinates_measurePreserving.restrict_preimage hD.measurableSet) (p := 2)
    simpa only [hp] using hh
  rw [he] at hb
  exact hb.trans_lt (mul_lt_mul_of_pos_left S.support_error (by norm_num))

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
