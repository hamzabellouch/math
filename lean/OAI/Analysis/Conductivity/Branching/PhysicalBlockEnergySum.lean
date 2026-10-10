import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalBlockEnergy

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma physicalBlockRegion_integral (f : (Fin 3 → ℝ) → ℝ)
    (hc : IntegrableOn f centralPhysical volume)
    (he : ∀ i : Fin 3,IntegrableOn f (physicalEndRegion i) volume) :
    (∫ y in physicalBlockRegion,f y)=(∫ y in centralPhysical,f y)+
      ∑ i : Fin 3,∫ y in physicalEndRegion i,f y := by
  have hci := hc.integrable_indicator centralPhysical_compact.measurableSet
  have hei (i : Fin 3) := (he i).integrable_indicator (physicalEndRegion_compact i).measurableSet
  rw [←integral_indicator physicalBlockRegion_compact.measurableSet]
  rw [integral_congr_ae (physicalBlockRegion_indicator_ae f)]
  rw [integral_add hci (integrable_finsetSum _ (fun i _ => hei i)),
    integral_finsetSum _ (fun i _ => hei i),
    integral_indicator centralPhysical_compact.measurableSet]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_indicator (physicalEndRegion_compact i).measurableSet

theorem physicalBlockTensor_energy_sum (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) (u v : H1) :
    Integrable (fun y => originalPiGradient u y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y)) (volume.restrict physicalBlockRegion) ∧
    (∫ y in physicalBlockRegion,originalPiGradient u y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y))=
      (∫ y in centralPhysical,originalPiGradient u y ⬝ᵥ originalPiGradient v y)+
      ∑ i : Fin 3,∫ y in physicalEndRegion i,originalPiGradient u y ⬝ᵥ
        (physicalEndTensor s a i y*ᵥoriginalPiGradient v y) := by
  refine ⟨physicalBlockTensor_weak_integrable s a hs ha
    physicalBlockRegion_compact.measurableSet (fun _ => physicalBlockRegion_subset_ball) u v,?_⟩
  rw [physicalBlockRegion_integral _
    (physicalBlockTensor_weak_integrable s a hs ha centralPhysical_compact.measurableSet
      (fun _ => centralPhysical_subset_ball) u v)
    (fun i => physicalBlockTensor_weak_integrable s a hs ha
      (physicalEndRegion_compact i).measurableSet
        (fun _ => physicalEndRegion_subset_ball i) u v),
    physicalBlockTensor_central_energy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact physicalBlockTensor_end_energy s a i (physicalEndRegion_compact i).measurableSet
    Subset.rfl u v

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceExpandedInner_bounds {y : Fin 3 → ℝ}
    (hy : -centralThickness ≤ sourceCollarTime y) :
    |y 0|≤1602/1000 ∧ |y 1|≤1001/1000 ∧ |y 2|≤1002/1000 := by
  have hh := (sourceCollarTime_ge_iff y (-centralThickness)).mp hy
  have hx := (le_max_left (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  have hy' := (le_max_right (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  norm_num [centralThickness,sourceRadialWidth,sourceHole,sourceLength] at hx hy' hh ⊢
  exact ⟨by linarith,by linarith,by linarith [hh.1]⟩

lemma sourceExpandedChild_far_parent (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : -centralThickness ≤ sourceCollarTime y) :
    2*centralThickness ≤ sourceCollarTime (sourceChildCoordinates (actualChildSign k) y) := by
  obtain ⟨h₀,h₁,h₂⟩ := sourceExpandedInner_bounds hy
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

lemma sourceExpandedChildren_exclusive (y : Fin 3 → ℝ)
    (h₀ : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign 0)).symm y))
    (h₁ : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign 1)).symm y)) : False := by
  have ha := (sourceExpandedInner_bounds h₀).2.1
  have hb := (sourceExpandedInner_bounds h₁).2.1
  change |(y 0 - actualChildSign 0 * sourceOffset)/sourceScale| ≤ _ at ha
  change |(y 0 - actualChildSign 1 * sourceOffset)/sourceScale| ≤ _ at hb
  norm_num [actualChildSign] at ha hb
  rw [abs_div,abs_of_pos (show 0<sourceScale by norm_num [sourceScale])] at ha hb
  have ha' := abs_le.mp ((div_le_iff₀ (show 0<sourceScale by norm_num [sourceScale])).mp ha)
  have hb' := abs_le.mp ((div_le_iff₀ (show 0<sourceScale by norm_num [sourceScale])).mp hb)
  norm_num [sourceScale,sourceOffset] at ha' hb'
  linarith [ha'.1,hb'.2]

lemma sourceExpandedChild_other (k j : Fin 2) (hkj : k≠j) {y : Fin 3 → ℝ}
    (hy : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)) :
    sourceCollarTime ((sourceChildHomeomorph (actualChildSign j)).symm y)< -centralThickness := by
  by_contra h
  have hj := le_of_not_gt h
  fin_cases k <;> fin_cases j
  · exact hkj rfl
  · exact sourceExpandedChildren_exclusive y hy hj
  · exact sourceExpandedChildren_exclusive y hj hy
  · exact hkj rfl

theorem physicalBlockRegion_time_iff (y : Fin 3 → ℝ) :
    y∈physicalBlockRegion ↔ 0≤ sourceCollarTime y ∧
      ∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)≤0 := by
  have hδ : 0<centralThickness := by norm_num [centralThickness]
  have hfar (k : Fin 2)
      (h : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)) :
      2*centralThickness≤ sourceCollarTime y := by
    have hh := sourceExpandedChild_far_parent k h
    have he : sourceChildCoordinates (actualChildSign k)
        ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
      (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
    rwa [he] at hh
  constructor
  · rintro (hc|he)
    · obtain ⟨hp,hc⟩ := (centralPhysical_time_iff y).mp hc
      exact ⟨hδ.le.trans hp,fun k => (hc k).trans (by linarith)⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp he
      revert hi
      refine Fin.cases ?_ (fun k => ?_) i
      · intro hi
        change sourceCollarTime y∈Icc 0 centralThickness at hi
        refine ⟨hi.1,fun k => ?_⟩
        by_contra hn
        have hh := hfar k (show -centralThickness≤ sourceCollarTime
            ((sourceChildHomeomorph (actualChildSign k)).symm y) by linarith [lt_of_not_ge hn])
        linarith [hi.2]
      · intro hi
        change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)
          ∈Icc (-centralThickness) 0 at hi
        refine ⟨(by linarith [hfar k hi.1]),fun j => ?_⟩
        by_cases hkj : k=j
        · simpa only [←hkj] using hi.2
        · exact (sourceExpandedChild_other k j hkj hi.1).le.trans (by linarith)
  · rintro ⟨hp,hc⟩
    by_cases ht : sourceCollarTime y≤centralThickness
    · exact physicalEndRegion_mem_block 0 ⟨hp,ht⟩
    · by_cases hh : ∀ k : Fin 2,sourceCollarTime
          ((sourceChildHomeomorph (actualChildSign k)).symm y)≤ -centralThickness
      · exact Or.inl ((centralPhysical_time_iff y).mpr ⟨(lt_of_not_ge ht).le,hh⟩)
      · push Not at hh
        obtain ⟨k,hk⟩ := hh
        exact physicalEndRegion_mem_block k.succ ⟨hk.le,hc k⟩

end ScalarConductivity

end

end OAI
