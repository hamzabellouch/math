import Mathlib
import OAI.Analysis.Conductivity.Sources.PhysicalBlockDomain

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceChild_toLp (σ : ℝ) (y : Fin 3 → ℝ) :
    WithLp.toLp 2 (sourceChildCoordinates σ y)=sourceSimilarity σ (WithLp.toLp 2 y) := by
  ext i
  fin_cases i
  · exact (sourceSimilarity_coord σ (WithLp.toLp 2 y)).1.symm
  · exact (sourceSimilarity_coord σ (WithLp.toLp 2 y)).2.1.symm
  · exact (sourceSimilarity_coord σ (WithLp.toLp 2 y)).2.2.symm

lemma sourceSimilarity_childInverse (σ : ℝ) (y : Fin 3 → ℝ) :
    sourceSimilarity σ (WithLp.toLp 2 ((sourceChildHomeomorph σ).symm y))=WithLp.toLp 2 y := by
  rw [←sourceChild_toLp]
  exact congrArg (WithLp.toLp 2) ((sourceChildHomeomorph σ).apply_symm_apply y)

lemma sourceChild_closure_image_iff (σ : ℝ) (y : Fin 3 → ℝ) :
    WithLp.toLp 2 y∈sourceSimilarity σ '' closure sourceDomain ↔
      0≤ sourceCollarTime ((sourceChildHomeomorph σ).symm y) := by
  rw [←sourceDomain_closure_time]
  constructor
  · rintro ⟨x,hx,he⟩
    have hh := (sourceSimilarity σ).injective (he.trans (sourceSimilarity_childInverse σ y).symm)
    rwa [←hh]
  · intro hy
    exact ⟨_,hy,sourceSimilarity_childInverse σ y⟩

def sourceOpenBlock : Set R3 := sourceDomain \ ⋃ k : Fin 2,
  sourceSimilarity (actualChildSign k) '' closure sourceDomain

lemma sourceOpenBlock_time_iff (y : Fin 3 → ℝ) :
    WithLp.toLp 2 y∈sourceOpenBlock ↔ 0<sourceCollarTime y ∧
      ∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)<0 := by
  simp only [sourceOpenBlock,Set.mem_sdiff,mem_iUnion,not_exists,
    ←sourceCollarTime_pos_iff_domain,sourceChild_closure_image_iff,not_le]

lemma sourceOpenBlock_isOpen : IsOpen sourceOpenBlock := by
  apply sourceDomain_isOpen.sdiff
  apply isClosed_iUnion_of_finite
  intro k
  exact ((sourceSimilarity (actualChildSign k)).isClosedMap _ isClosed_closure)

lemma physicalBlockRegion_openBlock_ae :
    physicalBlockRegion=ᵐ[volume] ((WithLp.toLp 2) ⁻¹' sourceOpenBlock) := by
  have hparent := sourceColevel_ae_ne (show (0:ℝ)∈Icc (-(1:ℝ)/100) (1/100) by norm_num)
  have hchild (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae hparent
  filter_upwards [hparent,hchild 0,hchild 1] with y hp hc₀ hc₁
  apply propext
  change y∈physicalBlockRegion ↔ y∈((WithLp.toLp 2) ⁻¹' sourceOpenBlock)
  rw [physicalBlockRegion_time_iff,mem_preimage,sourceOpenBlock_time_iff]
  have hc (k : Fin 2) : sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)≠0 := by
    fin_cases k
    · exact hc₀
    · exact hc₁
  constructor
  · rintro ⟨hp',hc'⟩
    exact ⟨lt_of_le_of_ne hp' hp.symm,fun k => lt_of_le_of_ne (hc' k) (hc k)⟩
  · rintro ⟨hp',hc'⟩
    exact ⟨hp'.le,fun k => (hc' k).le⟩

lemma physicalBlockRegion_openBlock_restrict :
    (volume : Measure (Fin 3 → ℝ)).restrict physicalBlockRegion=
      volume.restrict ((WithLp.toLp 2) ⁻¹' sourceOpenBlock) :=
  Measure.restrict_congr_set physicalBlockRegion_openBlock_ae

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

theorem sourceOpenBlock_tensor_energy (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) (u v : H1) :
    Integrable (fun y => originalPiGradient u y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y))
        (volume.restrict ((WithLp.toLp 2) ⁻¹' sourceOpenBlock)) ∧
    (∫ y in (WithLp.toLp 2) ⁻¹' sourceOpenBlock,originalPiGradient u y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y))=
      (∫ y in centralPhysical,originalPiGradient u y ⬝ᵥ originalPiGradient v y)+
      ∑ i : Fin 3,∫ y in physicalEndRegion i,originalPiGradient u y ⬝ᵥ
        (physicalEndTensor s a i y*ᵥoriginalPiGradient v y) := by
  rw [←physicalBlockRegion_openBlock_restrict]
  exact physicalBlockTensor_energy_sum s a hs ha u v

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceOpenBlock_parent_band {y : Fin 3 → ℝ}
    (hp : 0<sourceCollarTime y) (ht : sourceCollarTime y<centralThickness) :
    WithLp.toLp 2 y∈sourceOpenBlock := by
  apply (sourceOpenBlock_time_iff y).mpr
  refine ⟨hp,fun k => ?_⟩
  by_contra hn
  have hc : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y) :=
    (show -centralThickness≤(0:ℝ) by norm_num [centralThickness]).trans (le_of_not_gt hn)
  have hfar := sourceExpandedChild_far_parent k hc
  have he : sourceChildCoordinates (actualChildSign k)
      ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
  rw [he] at hfar
  norm_num [centralThickness] at ht hfar
  linarith

lemma sourceOpenBlock_child_band (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : -centralThickness ≤ sourceCollarTime y) (ht : sourceCollarTime y<0) :
    WithLp.toLp 2 (sourceChildCoordinates (actualChildSign k) y)∈sourceOpenBlock := by
  apply (sourceOpenBlock_time_iff _).mpr
  refine ⟨lt_of_lt_of_le (show (0:ℝ)<2*centralThickness by norm_num [centralThickness])
    (sourceExpandedChild_far_parent k hy),fun j => ?_⟩
  have he : (sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply y
  by_cases hkj : k=j
  · rw [←hkj,he]
    exact ht
  · exact (sourceExpandedChild_other k j hkj (show -centralThickness ≤ sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm
        (sourceChildCoordinates (actualChildSign k) y)) by rw [he]; exact hy)).trans
      (by norm_num [centralThickness])

lemma physicalBlockRegion_mem_closure_openBlock {y : Fin 3 → ℝ}
    (hy : y∈physicalBlockRegion) :
    y∈closure ((WithLp.toLp 2) ⁻¹' sourceOpenBlock) := by
  obtain ⟨hp,hc⟩ := (physicalBlockRegion_time_iff y).mp hy
  by_cases h0 : sourceCollarTime y=0
  · let g : ℝ → (Fin 3 → ℝ) := fun t => sourceAngularCollar t (sourcePhysicalAngles y)
    have hg : Continuous g := continuous_uncurry_sourceAngularCollar.comp
      (continuous_id.prodMk continuous_const)
    have hz : (0:ℝ)∈closure (Ioo 0 centralThickness) := by
      rw [closure_Ioo (show (0:ℝ)≠centralThickness by norm_num [centralThickness])]
      exact ⟨le_rfl,by norm_num [centralThickness]⟩
    have hin : g '' Ioo 0 centralThickness ⊆ (WithLp.toLp 2) ⁻¹' sourceOpenBlock := by
      rintro _ ⟨t,ht,rfl⟩
      have he := sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
        ⟨by linarith [ht.1],ht.2.le.trans (by norm_num [centralThickness])⟩) (sourcePhysicalAngles y)
      exact sourceOpenBlock_parent_band (by dsimp [g]; rw [he]; exact ht.1) (by dsimp [g]; rw [he]; exact ht.2)
    have hmem := closure_mono hin (image_closure_subset_closure_image hg ⟨0,hz,rfl⟩)
    have he := sourcePhysicalCoordinates_right
      (show sourceCollarTime y∈Icc (-(1:ℝ)/100) (1/100) by rw [h0]; norm_num)
    rw [h0] at he
    simpa only [g,he] using hmem
  · by_cases hchild : ∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)≠0
    · exact subset_closure ((sourceOpenBlock_time_iff y).mpr
        ⟨lt_of_le_of_ne hp (Ne.symm h0),fun k => lt_of_le_of_ne (hc k) (hchild k)⟩)
    · push Not at hchild
      obtain ⟨k,hk⟩ := hchild
      let z := (sourceChildHomeomorph (actualChildSign k)).symm y
      let g : ℝ → (Fin 3 → ℝ) := fun t => sourceChildCoordinates (actualChildSign k)
        (sourceAngularCollar t (sourcePhysicalAngles z))
      have hg : Continuous g := (sourceChildCoordinates_contDiff _).continuous.comp
        (continuous_uncurry_sourceAngularCollar.comp (continuous_id.prodMk continuous_const))
      have hz : (0:ℝ)∈closure (Ioo (-centralThickness) 0) := by
        rw [closure_Ioo (show -centralThickness≠(0:ℝ) by norm_num [centralThickness])]
        exact ⟨by norm_num [centralThickness],le_rfl⟩
      have hin : g '' Ioo (-centralThickness) 0 ⊆ (WithLp.toLp 2) ⁻¹' sourceOpenBlock := by
        rintro _ ⟨t,ht,rfl⟩
        apply sourceOpenBlock_child_band k
        · rw [sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
            ⟨(show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans ht.1.le,
              ht.2.le.trans (by norm_num)⟩)]
          exact ht.1.le
        · rw [sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
            ⟨(show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans ht.1.le,
              ht.2.le.trans (by norm_num)⟩)]
          exact ht.2
      have hmem := closure_mono hin (image_closure_subset_closure_image hg ⟨0,hz,rfl⟩)
      have he := sourcePhysicalCoordinates_right
        (show sourceCollarTime z∈Icc (-(1:ℝ)/100) (1/100) by
          change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)∈_
          rw [hk]
          norm_num)
      change sourceAngularCollar (sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y))
        (sourcePhysicalAngles z)=z at he
      rw [hk] at he
      have he' : sourceChildCoordinates (actualChildSign k) z=y :=
        (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
      simpa only [g,he,he'] using hmem

theorem physicalBlockRegion_eq_closure_openBlock : physicalBlockRegion=
    closure ((WithLp.toLp 2) ⁻¹' sourceOpenBlock) := by
  apply Subset.antisymm (fun y hy => physicalBlockRegion_mem_closure_openBlock hy)
  apply closure_minimal _ physicalBlockRegion_compact.isClosed
  intro y hy
  obtain ⟨hp,hc⟩ := (sourceOpenBlock_time_iff y).mp hy
  exact (physicalBlockRegion_time_iff y).mpr ⟨hp.le,fun k => (hc k).le⟩

end ScalarConductivity

end

end OAI
