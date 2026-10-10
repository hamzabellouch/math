import OAI.Analysis.CircleDomains.Sobolev.ComplexWeakGradient
import OAI.Analysis.CircleDomains.Transfer.ModelFlattenedSelection
import OAI.Analysis.CircleDomains.Transfer.ModelWorkingCoordinates

namespace OAI

/-! Transfer the selected priority error to the actual compact source
Sobolev witness. On the working disk the source cutoff is one. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem priority_weak_error (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d A L δ ε : ℝ} (H : ControlledHeight R d)
    {W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H W A L δ ε)
    (η : ℂ → ℝ)
    (hη : ∀ z ∈ {z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L, η z = 1)
    (Wp : DeGiorgi.MemW1pWitness 2
      (fun x => η (complexPlaneCoordinates x)*priorityInfiniteValue
        (fun n => S.cutoff n (complexPlaneCoordinates x)) S.value
        (M.horizontalSection (planeSphere x))) (physicalPlaneDomain G ∩ ball 0 L))
    (Wx : DeGiorgi.MemW1pWitness 2
      (fun x => (M.function (complexPlaneCoordinates x)).re) (physicalPlaneDomain G ∩ ball 0 L)) :
    (eLpNorm (fun x => Wp.weakGrad x-Wx.weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal < ε := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  let V := D ∩ ball (0 : ℂ) L
  let X := fun z : ℂ => M.horizontalSection (z : Sphere)
  let P := fun z : ℂ => priorityInfiniteValue (fun n => S.cutoff n z) S.value (X z)
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hV : IsOpen V := hD.inter isOpen_ball
  have he : complexPlaneCoordinates ⁻¹' V = physicalPlaneDomain G ∩ ball 0 L := by
    ext x
    simp only [mem_preimage, mem_inter_iff, V, D, mem_ofPred_eq, mem_ball,
      dist_zero_right, complexPlaneCoordinates_norm]
    rfl
  have hXs : ContDiffOn ℝ ∞ X V := (M.horizontalSection_plane_smooth hG).mono inter_subset_left
  have hPs : ContDiffOn ℝ ∞ P V := by
    have hh := priorityInfiniteValue_smooth_off_dust hD.isClosed_compl S.center
      S.center_outside S.radius S.radius_tendsto S.cutoff S.cutoff_smooth S.cutoff_support
      S.value X (by simpa only [compl_compl] using M.horizontalSection_plane_smooth hG)
    exact (show ContDiffOn ℝ ∞ P D from by simpa only [compl_compl] using hh).mono inter_subset_left
  have hXE : MemLp (fderiv ℝ X) 2 (volume.restrict V) := M.horizontalSection_plane_memLp hG hinf L
  have hPE : MemLp (fderiv ℝ P) 2 (volume.restrict V) := by
    have hmaj := S.priority_error_memLp.norm.add hXE.norm
    apply hmaj.of_le
      ((hPs.continuousOn_fderiv_of_isOpen hV (by simp)).aestronglyMeasurable hV.measurableSet)
    exact Eventually.of_forall (fun z => by
      change ‖fderiv ℝ P z‖ ≤ ‖‖fderiv ℝ P z-fderiv ℝ X z‖+‖fderiv ℝ X z‖‖
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      calc
        _ = ‖(fderiv ℝ P z-fderiv ℝ X z)+fderiv ℝ X z‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _)
  let WP : DeGiorgi.MemW1pWitness 2 (P ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' V) := by
    apply localSobolevChangeDomain (V := complexPlaneCoordinates ⁻¹' V) (Wp.congr_ae ?_) he.symm
    filter_upwards [ae_restrict_mem ((isOpen_physicalPlaneDomain hG).inter isOpen_ball).measurableSet] with x hx
    change η (complexPlaneCoordinates x)*P (complexPlaneCoordinates x) = P (complexPlaneCoordinates x)
    rw [hη _ ⟨hx.1, by simpa only [mem_ball, dist_zero_right, complexPlaneCoordinates_norm] using hx.2⟩, one_mul]
  let WX : DeGiorgi.MemW1pWitness 2 (X ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' V) := by
    apply localSobolevChangeDomain (V := complexPlaneCoordinates ⁻¹' V) (Wx.congr_ae ?_) he.symm
    filter_upwards [ae_restrict_mem ((isOpen_physicalPlaneDomain hG).inter isOpen_ball).measurableSet] with x hx
    exact (show X (complexPlaneCoordinates x) = (M.function (complexPlaneCoordinates x)).re from by
      simpa only [X, planeSphere, extendAtInfinity_coe, finiteCoord_coe] using M.horizontalSection_on_domain hx.1).symm
  have hn := complex_weak_gradient_difference_L2 hV hPs hXs hPE hXE WP WX
  have hgradP : WP.weakGrad = Wp.weakGrad := by rfl
  have hgradX : WX.weakGrad = Wx.weakGrad := by rfl
  rw [hgradP, hgradX, he] at hn
  rw [hn]
  exact S.priority_error

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
