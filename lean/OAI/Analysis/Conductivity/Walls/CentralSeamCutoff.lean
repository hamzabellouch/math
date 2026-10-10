import Mathlib
import OAI.Analysis.Conductivity.Branching.CentralJoinCover

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceJoinInner_bounds {y : Fin 3 → ℝ}
    (hy : -2*centralThickness ≤ sourceCollarTime y) :
    |y 0|≤1604/1000 ∧ |y 1|≤1002/1000 ∧ |y 2|≤1004/1000 := by
  have hh := (sourceCollarTime_ge_iff y (-2*centralThickness)).mp hy
  have hx := (le_max_left (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  have hy' := (le_max_right (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  norm_num [centralThickness,sourceRadialWidth,sourceHole,sourceLength] at hx hy' hh ⊢
  exact ⟨by linarith,by linarith,by linarith [hh.1]⟩

lemma sourceJoinChild_far_parent (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : -2*centralThickness ≤ sourceCollarTime y) :
    2*centralThickness ≤ sourceCollarTime (sourceChildCoordinates (actualChildSign k) y) := by
  obtain ⟨h₀,h₁,h₂⟩ := sourceJoinInner_bounds hy
  have hsign : |actualChildSign k|=1 := by fin_cases k <;> norm_num [actualChildSign]
  have ha : |actualChildSign k*sourceOffset|=sourceOffset := by
    rw [abs_mul,hsign,one_mul]; norm_num [sourceOffset]
  have hu := abs_add_le (sourceScale*y 1) (actualChildSign k*sourceOffset)
  rw [abs_mul,abs_of_pos (show 0<sourceScale by norm_num [sourceScale]),ha] at hu
  have hl := abs_add_le (-sourceScale*y 1) (sourceScale*y 1+actualChildSign k*sourceOffset)
  have he : -sourceScale*y 1+(sourceScale*y 1+actualChildSign k*sourceOffset)=
    actualChildSign k*sourceOffset := by ring
  rw [he,ha,abs_mul,abs_neg,abs_of_pos (show 0<sourceScale by norm_num [sourceScale])] at hl
  apply (sourceCollarTime_ge_iff _ _).mpr
  change |sourceScale*y 2|≤_ ∧ _≤ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
    (|sourceScale*y 0|) ∧ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
      (|sourceScale*y 0|)≤_
  simp only [abs_mul,abs_of_pos (show 0<sourceScale by norm_num [sourceScale])]
  constructor
  · norm_num [sourceScale,centralThickness]; linarith
  · constructor
    · apply le_trans _ (le_max_left _ _)
      norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
      linarith
    · apply max_le
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith

lemma centralPhysical_parent_face_not_interior {y : Fin 3 → ℝ}
    (hy : sourceCollarTime y=centralThickness) : y∉interior centralPhysical := by
  let g : ℝ → (Fin 3 → ℝ) := fun t => sourceAngularCollar t (sourcePhysicalAngles y)
  have hg : Continuous g := continuous_uncurry_sourceAngularCollar.comp
    (continuous_id.prodMk continuous_const)
  have hz : centralThickness∈closure (Ioo 0 centralThickness) := by
    rw [closure_Ioo (show (0:ℝ)≠centralThickness by norm_num [centralThickness])]
    exact ⟨by norm_num [centralThickness],le_rfl⟩
  have hin : g '' Ioo 0 centralThickness ⊆ (interior centralPhysical)ᶜ := by
    rintro _ ⟨t,ht,rfl⟩ hn
    have he := sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
      ⟨by linarith [ht.1],ht.2.le.trans (by norm_num [centralThickness])⟩) (sourcePhysicalAngles y)
    have hp := ((centralPhysical_time_iff (g t)).mp (interior_subset hn)).1
    change centralThickness ≤ sourceCollarTime (sourceAngularCollar t (sourcePhysicalAngles y)) at hp
    rw [he] at hp
    exact (not_le_of_gt ht.2) hp
  have hmem := closure_minimal hin isOpen_interior.isClosed_compl
    (image_closure_subset_closure_image hg ⟨centralThickness,hz,rfl⟩)
  have he := sourcePhysicalCoordinates_right
    (show sourceCollarTime y∈Icc (-(1:ℝ)/100) (1/100) by rw [hy]; norm_num [centralThickness])
  rw [hy] at he
  simpa only [g,he,Set.mem_compl_iff] using hmem

lemma centralJoinPartition_parent_one {y : Fin 3 → ℝ}
    (hy : sourceCollarTime y=centralThickness) :
    centralJoinPartition 1=ᶠ[𝓝 y] (fun _ => 1) := by
  have hc : y∈centralPhysical := parentBand_central
    (show y∈sourceClosedCollarBand centralThickness (2*centralThickness) by
      change sourceCollarTime y∈Icc centralThickness (2*centralThickness)
      rw [hy]; constructor <;> norm_num [centralThickness])
  have hi : y∉tsupport (centralJoinPartition 0) := fun h =>
    centralPhysical_parent_face_not_interior hy (centralJoinPartition_subordinate 0 h)
  have hj (k : Fin 2) : y∉tsupport (centralJoinPartition (centralChildPatch k)) := by
    intro h
    have hlocal := centralJoinPartition_subordinate (centralChildPatch k) h
    have ht : -2*centralThickness ≤ sourceCollarTime
        ((sourceChildHomeomorph (actualChildSign k)).symm y) := by
      fin_cases k
      · change sourceCollarTime ((sourceChildHomeomorph 1).symm y)∈Ioo (-2*centralThickness) 0 at hlocal
        exact hlocal.1.le
      · change sourceCollarTime ((sourceChildHomeomorph (-1)).symm y)∈Ioo (-2*centralThickness) 0 at hlocal
        exact hlocal.1.le
    have hp := sourceJoinChild_far_parent k ht
    have he : sourceChildCoordinates (actualChildSign k)
        ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
      (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
    rw [he,hy] at hp
    norm_num [centralThickness] at hp
  have h₀ := notMem_tsupport_iff_eventuallyEq.mp hi
  have h₂ := notMem_tsupport_iff_eventuallyEq.mp (hj 0)
  have h₃ := notMem_tsupport_iff_eventuallyEq.mp (hj 1)
  filter_upwards [centralJoinPartition_eventually_sum hc,h₀,h₂,h₃] with z hz h₀ h₂ h₃
  change centralJoinPartition 0 z=0 at h₀
  change centralJoinPartition 2 z=0 at h₂
  change centralJoinPartition 3 z=0 at h₃
  simpa only [Fin.sum_univ_four,h₀,h₂,h₃,zero_add,add_zero] using hz

end ScalarConductivity

end

end OAI
