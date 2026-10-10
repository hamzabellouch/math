import Mathlib
import OAI.Analysis.Conductivity.Walls.CentralSeamCutoff

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceJoinChildren_exclusive (y : Fin 3 → ℝ)
    (h₀ : -2*centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign 0)).symm y))
    (h₁ : -2*centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign 1)).symm y)) : False := by
  have ha := (sourceJoinInner_bounds h₀).2.1
  have hb := (sourceJoinInner_bounds h₁).2.1
  change |(y 0 - actualChildSign 0 * sourceOffset)/sourceScale| ≤ _ at ha
  change |(y 0 - actualChildSign 1 * sourceOffset)/sourceScale| ≤ _ at hb
  norm_num [actualChildSign] at ha hb
  rw [abs_div,abs_of_pos (show 0<sourceScale by norm_num [sourceScale])] at ha hb
  have ha' := abs_le.mp ((div_le_iff₀ (show 0<sourceScale by norm_num [sourceScale])).mp ha)
  have hb' := abs_le.mp ((div_le_iff₀ (show 0<sourceScale by norm_num [sourceScale])).mp hb)
  norm_num [sourceScale,sourceOffset] at ha' hb'
  linarith [ha'.1,hb'.2]

lemma sourceJoinChild_other (k j : Fin 2) (hkj : k≠j) {y : Fin 3 → ℝ}
    (hy : -2*centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)) :
    sourceCollarTime ((sourceChildHomeomorph (actualChildSign j)).symm y)< -2*centralThickness := by
  by_contra h
  have hj := le_of_not_gt h
  fin_cases k <;> fin_cases j
  · exact hkj rfl
  · exact sourceJoinChildren_exclusive y hy hj
  · exact sourceJoinChildren_exclusive y hj hy
  · exact hkj rfl

lemma centralPhysical_child_face_not_interior (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)= -centralThickness) :
    y∉interior centralPhysical := by
  let z := (sourceChildHomeomorph (actualChildSign k)).symm y
  let g : ℝ → (Fin 3 → ℝ) := fun t => sourceChildCoordinates (actualChildSign k)
    (sourceAngularCollar t (sourcePhysicalAngles z))
  have hg : Continuous g := (sourceChildCoordinates_contDiff _).continuous.comp
    (continuous_uncurry_sourceAngularCollar.comp (continuous_id.prodMk continuous_const))
  have hz : -centralThickness∈closure (Ioo (-centralThickness) 0) := by
    rw [closure_Ioo (show -centralThickness≠(0:ℝ) by norm_num [centralThickness])]
    exact ⟨le_rfl,by norm_num [centralThickness]⟩
  have hin : g '' Ioo (-centralThickness) 0 ⊆ (interior centralPhysical)ᶜ := by
    rintro _ ⟨t,ht,rfl⟩ hn
    have he := sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
      ⟨(show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans ht.1.le,
        by linarith [ht.2]⟩) (sourcePhysicalAngles z)
    have hp := ((centralPhysical_time_iff (g t)).mp (interior_subset hn)).2 k
    have hi : (sourceChildHomeomorph (actualChildSign k)).symm (g t)=
        sourceAngularCollar t (sourcePhysicalAngles z) :=
      (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply _
    rw [hi,he] at hp
    exact (not_le_of_gt ht.1) hp
  have hmem := closure_minimal hin isOpen_interior.isClosed_compl
    (image_closure_subset_closure_image hg ⟨-centralThickness,hz,rfl⟩)
  have he := sourcePhysicalCoordinates_right
    (show sourceCollarTime z∈Icc (-(1:ℝ)/100) (1/100) by
      change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)∈_
      rw [hy]
      norm_num [centralThickness])
  change sourceAngularCollar (sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y))
    (sourcePhysicalAngles z)=z at he
  rw [hy] at he
  have he' : sourceChildCoordinates (actualChildSign k) z=y :=
    (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
  simpa only [g,he,he',Set.mem_compl_iff] using hmem

lemma centralJoinPartition_child_one (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)= -centralThickness) :
    centralJoinPartition (centralChildPatch k)=ᶠ[𝓝 y] (fun _ => 1) := by
  have hb : (sourceChildHomeomorph (actualChildSign k)).symm y∈
      sourceClosedCollarBand (-2*centralThickness) (-centralThickness) := by
    change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)∈Icc _ _
    rw [hy]; constructor <;> norm_num [centralThickness]
  have he : sourceChildCoordinates (actualChildSign k)
      ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
  have hc : y∈centralPhysical := by
    have hh := childBand_central k hb
    rw [he] at hh
    exact hh
  have hi : y∉tsupport (centralJoinPartition 0) := fun h =>
    centralPhysical_child_face_not_interior k hy (centralJoinPartition_subordinate 0 h)
  have hfar := sourceJoinChild_far_parent k hb.1
  rw [he] at hfar
  have hp : y∉tsupport (centralJoinPartition 1) := by
    intro h
    have hh := centralJoinPartition_subordinate 1 h
    change sourceCollarTime y∈Ioo 0 (2*centralThickness) at hh
    exact (not_lt_of_ge hfar) hh.2
  have hj (j : Fin 2) (hjk : k≠j) : y∉tsupport (centralJoinPartition (centralChildPatch j)) := by
    intro h
    have hh := centralJoinPartition_subordinate (centralChildPatch j) h
    have hlocal : -2*centralThickness < sourceCollarTime
        ((sourceChildHomeomorph (actualChildSign j)).symm y) := by
      fin_cases j
      · change sourceCollarTime ((sourceChildHomeomorph 1).symm y)∈Ioo (-2*centralThickness) 0 at hh
        exact hh.1
      · change sourceCollarTime ((sourceChildHomeomorph (-1)).symm y)∈Ioo (-2*centralThickness) 0 at hh
        exact hh.1
    exact (not_lt_of_ge (sourceJoinChild_other k j hjk hb.1).le) hlocal
  have h₀ := notMem_tsupport_iff_eventuallyEq.mp hi
  have h₁ := notMem_tsupport_iff_eventuallyEq.mp hp
  have hsum := centralJoinPartition_eventually_sum hc
  fin_cases k
  · have hother := notMem_tsupport_iff_eventuallyEq.mp (hj 1 (by decide))
    filter_upwards [h₀,h₁,hsum,hother] with z h₀ h₁ hz h₃
    change centralJoinPartition 0 z=0 at h₀
    change centralJoinPartition 1 z=0 at h₁
    change centralJoinPartition 3 z=0 at h₃
    change centralJoinPartition 2 z=1
    simpa only [Fin.sum_univ_four,h₀,h₁,h₃,zero_add,add_zero] using hz
  · have hother := notMem_tsupport_iff_eventuallyEq.mp (hj 0 (by decide))
    filter_upwards [h₀,h₁,hsum,hother] with z h₀ h₁ hz h₂
    change centralJoinPartition 0 z=0 at h₀
    change centralJoinPartition 1 z=0 at h₁
    change centralJoinPartition 2 z=0 at h₂
    change centralJoinPartition 3 z=1
    simpa only [Fin.sum_univ_four,h₀,h₁,h₂,zero_add,add_zero] using hz

lemma centralJoinChildCutoff_one (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : sourceCollarTime y= -centralThickness) :
    centralJoinChildCutoff k=ᶠ[𝓝 y] (fun _ => 1) := by
  have he : (sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply y
  have hh := centralJoinPartition_child_one k
    (show sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y))= -centralThickness by rw [he]; exact hy)
  exact hh.comp_tendsto (sourceChildCoordinates_contDiff _).continuous.continuousAt

end ScalarConductivity

end

end OAI
