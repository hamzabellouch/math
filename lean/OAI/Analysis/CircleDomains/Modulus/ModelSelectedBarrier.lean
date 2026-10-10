import OAI.Analysis.CircleDomains.Sobolev.ModelPriorityWeakError
import OAI.Analysis.CircleDomains.Transfer.ModelSelectedSupport
import OAI.Analysis.CircleDomains.Transfer.ModelPairWorkingError
import OAI.Analysis.CircleDomains.Sobolev.LocalWeakBarrierBound

namespace OAI

/-! The actual selected compact source pair satisfies the quantitative
barrier comparison. Its horizontal, vertical and support terms are
proved from the selection and transported height-error witness. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem selected_barrier_error (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d A L δ ε : ℝ} (H : ControlledHeight R d)
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L δ ε)
    (η : ℂ → ℝ) (θ : EuclideanPlane → ℝ)
    (hη : ∀ z ∈ {z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L, η z = 1)
    (hθ : ∀ x ∈ physicalPlaneDomain G ∩ ball 0 L,
      θ (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1)
    (hp : Continuous (M.compactPrioritySource S.cutoff S.value η))
    (hq : Continuous (M.compactHeightSource H (flattenValues S.heightValues) θ))
    (Wp : DeGiorgi.MemW1pWitness 2 (M.compactPrioritySource S.cutoff S.value η)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wq : DeGiorgi.MemW1pWitness 2 (M.compactHeightSource H (flattenValues S.heightValues) θ)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L))
    (E : DeGiorgi.MemW1pWitness 2 (planeInverseTransport (extendAtInfinity M.function)
      (fun y => θ y*(flattenValues S.heightValues (H.height (complexPlaneCoordinates y))-y 1)))
      (physicalPlaneDomain G))
    {ν δv : ℝ} (hν : 0 ≤ ν) (hδ : 0 ≤ δ) (hδv : 0 ≤ δv)
    (hE : (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) ≤ ν^2)
    (hheight : ∀ x ∈ physicalPlaneDomain G ∩ ball 0 L,
      |H.height (M.function (complexPlaneCoordinates x))-(M.function (complexPlaneCoordinates x)).im| ≤ δv)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B M₁ M₂ : ℝ} (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hΦb : ∀ z, ‖Φ z‖ ≤ B) (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ M₁)
    (hlip : ∀ z w, ‖fderiv ℝ Φ z-fderiv ℝ Φ w‖ ≤ M₂*‖z-w‖) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair
        (M.compactPrioritySource S.cutoff S.value η x)
        (M.compactHeightSource H (flattenValues S.heightValues) θ x)))
      (physicalPlaneDomain G ∩ ball 0 L),
      (eLpNorm (fun x => W.weakGrad x-planeCovectorGradient
        ((fderiv ℝ Φ (planePair ((M.function (complexPlaneCoordinates x)).re)
          ((M.function (complexPlaneCoordinates x)).im))).comp
          (weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)))) 2
            (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤
      M₁*(ε+ν)+(M₂*(δ+δv))*(eLpNorm
        (fun x => weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)) 2
          (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal+4*M₁*ε := by
  let U := physicalPlaneDomain G ∩ ball (0 : EuclideanPlane) L
  let C := complexPlaneCoordinates ⁻¹' ⋃ n, support (S.cutoff n)
  have hU : IsOpen U := (isOpen_physicalPlaneDomain hG).inter isOpen_ball
  have hUf : volume U ≠ (⊤ : ℝ≥0∞) := ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hC : MeasurableSet C := (MeasurableSet.iUnion
    (fun n => (S.cutoff_smooth n).continuous.isOpen_support.measurableSet)).preimage
      complexPlaneCoordinates.continuous.measurable
  have hpE := M.priority_weak_error hG hinf H S η hη Wp Wx
  have hqE := M.compact_height_source_error_L2 H (flattenValues S.heightValues) θ
    hU inter_subset_left hθ Wq Wy E hE
  have hqE' : (eLpNorm (fun x => Wq.weakGrad x-Wy.weakGrad x) 2 (volume.restrict U)).toReal ≤ ν := by
    nlinarith [ENNReal.toReal_nonneg (a := eLpNorm (fun x => Wq.weakGrad x-Wy.weakGrad x) 2 (volume.restrict U))]
  have hsE := M.selected_support_error hG hinf H S Wx Wy
  obtain ⟨W,hW,hn⟩ := local_weak_barrier_bound hU hUf hC hp hq Wp Wq Wx Wy
    hΦ hB hM₁ hM₂ (add_nonneg hδ hδv) hΦb hbound hlip (fun x hx hxc =>
      M.compact_pair_error_outside_support H (flattenValues S.heightValues)
        (fun t => (S.height_close t).le) η θ S.cutoff S.value hx.1
        (hη _ ⟨hx.1, by simpa only [mem_ball, dist_zero_right, complexPlaneCoordinates_norm] using hx.2⟩)
        (hθ x hx) (hheight x hx) hxc)
  refine ⟨W,hn.trans ?_⟩
  have h₁ := mul_le_mul_of_nonneg_left (add_le_add hpE.le hqE') hM₁
  have h₂ := mul_le_mul_of_nonneg_left hsE.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM₁)
  calc
    _ ≤ M₁*(ε+ν)+(M₂*(δ+δv))*(eLpNorm
        (fun x => weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)) 2
        (volume.restrict U)).toReal+(2*M₁)*(2*ε) :=
      add_le_add (add_le_add h₁ le_rfl) h₂
    _ = _ := by ring

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
