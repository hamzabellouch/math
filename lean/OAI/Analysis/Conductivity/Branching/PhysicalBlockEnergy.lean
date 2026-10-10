import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalChildIntegral
import OAI.Analysis.Conductivity.Flux.PhysicalBlockTensor

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma physicalBlockTensor_central_ae (s a : Fin 3 → ℝ) :
    ∀ᵐ y∂(volume : Measure (Fin 3 → ℝ)),y∈centralPhysical → physicalBlockTensor s a y=1 := by
  have hparent := sourceColevel_ae_ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
  have hchild (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae
    (sourceColevel_ae_ne
      (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness]))
  filter_upwards [hparent,hchild 0,hchild 1] with y hp hc₀ hc₁ hy
  apply physicalBlockTensorList_outside
  intro i _ hi
  have ht := (centralPhysical_time_iff y).mp hy
  have hn (k : Fin 2) : sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm y)≠-centralThickness := by
    fin_cases k
    · exact hc₀
    · exact hc₁
  fin_cases i
  · change sourceCollarTime y∈Icc 0 centralThickness at hi
    exact hp (le_antisymm hi.2 ht.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 0)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hn 0 (le_antisymm (ht.2 0) hi.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 1)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hn 1 (le_antisymm (ht.2 1) hi.1)

lemma physicalBlockTensor_entry_memLp (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) (i j : Fin 3) :
    MemLp (fun y => physicalBlockTensor s a y i j) ∞
      (volume : Measure (Fin 3 → ℝ)) := by
  have h := physicalBlockTensor_properties s a hs ha
  let heval : (Matrix (Fin 3) (Fin 3) ℝ) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.proj j) : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
      ((ContinuousLinearMap.proj i) : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (Fin 3 → ℝ))
  exact heval.comp_memLp' h.2.1

theorem physicalBlockTensor_weak_integrable (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u v : H1) :
    Integrable (fun y => originalPiGradient u y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y)) (volume.restrict D) := by
  have hrow (i : Fin 3) : MemLp (fun y => ∑ j : Fin 3,
      physicalBlockTensor s a y i j*originalPiGradient v y j) 2 (volume.restrict D) := by
    apply memLp_finsetSum
    intro j _
    exact ((physicalBlockTensor_entry_memLp s a hs ha i j).restrict D).mul (r := 2)
      (originalPiGradient_memLp_on_ball hD hb v j)
  change Integrable (fun y => ∑ i : Fin 3,originalPiGradient u y i*
    ∑ j : Fin 3,physicalBlockTensor s a y i j*originalPiGradient v y j) _
  apply integrable_finsetSum
  intro i _
  exact (originalPiGradient_memLp_on_ball hD hb u i).integrable_mul (hrow i)

lemma physicalBlockTensor_end_energy (s a : Fin 3 → ℝ) (i : Fin 3)
    {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D) (hsub : D⊆physicalEndRegion i)
    (u v : H1) :
    (∫ y in D,originalPiGradient u y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y))=
    ∫ y in D,originalPiGradient u y ⬝ᵥ
      (physicalEndTensor s a i y*ᵥoriginalPiGradient v y) := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hD] with y hy
  rw [physicalBlockTensor_local s a i (hsub hy)]

lemma physicalBlockTensor_central_energy (s a : Fin 3 → ℝ) (u v : H1) :
    (∫ y in centralPhysical,originalPiGradient u y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y))=
    ∫ y in centralPhysical,originalPiGradient u y ⬝ᵥ originalPiGradient v y := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (physicalBlockTensor_central_ae s a),
    ae_restrict_mem centralPhysical_compact.measurableSet] with y he hy
  rw [he hy,Matrix.one_mulVec]

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def physicalBlockRegion : Set (Fin 3 → ℝ) :=
  centralPhysical ∪ ⋃ i : Fin 3,physicalEndRegion i

lemma physicalBlockRegion_compact : IsCompact physicalBlockRegion :=
  centralPhysical_compact.union (isCompact_iUnion physicalEndRegion_compact)

lemma physicalEndRegion_subset_ball (i : Fin 3) {y : Fin 3 → ℝ}
    (hy : y∈physicalEndRegion i) : WithLp.toLp 2 y∈ball := by
  revert hy
  refine Fin.cases ?_ (fun k => ?_) i
  · intro hy
    exact sourceBand_mem_ball ⟨(show -(1:ℝ)/100≤0 by norm_num).trans hy.1,
      hy.2.trans (by norm_num [centralThickness])⟩
  · intro hy
    apply sourceChild_image_ball (D := sourceClosedCollarBand (-centralThickness) 0) k
      (fun z hz => sourceBand_mem_ball
      ⟨(show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans hz.1,
        hz.2.trans (show (0:ℝ)≤1/100 by norm_num)⟩) y
    exact ⟨(sourceChildHomeomorph (actualChildSign k)).symm y,hy,
      (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y⟩

lemma physicalBlockRegion_subset_ball {y : Fin 3 → ℝ} (hy : y∈physicalBlockRegion) :
    WithLp.toLp 2 y∈ball := by
  rcases hy with hc|he
  · exact centralPhysical_subset_ball hc
  · obtain ⟨i,hi⟩ := mem_iUnion.mp he
    exact physicalEndRegion_subset_ball i hi

lemma physicalEndRegion_mem_block (i : Fin 3) : physicalEndRegion i⊆physicalBlockRegion :=
  fun _ hy => Or.inr (mem_iUnion.mpr ⟨i,hy⟩)

lemma physicalBlockRegion_central_end_exclusive_ae :
    ∀ᵐ y∂(volume : Measure (Fin 3 → ℝ)),
      y∈centralPhysical → ∀ i : Fin 3,y∉physicalEndRegion i := by
  have hparent := sourceColevel_ae_ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
  have hchild (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae
    (sourceColevel_ae_ne
      (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness]))
  filter_upwards [hparent,hchild 0,hchild 1] with y hp hc₀ hc₁ hy i hi
  have ht := (centralPhysical_time_iff y).mp hy
  fin_cases i
  · change sourceCollarTime y∈Icc 0 centralThickness at hi
    exact hp (le_antisymm hi.2 ht.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 0)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hc₀ (le_antisymm (ht.2 0) hi.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 1)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hc₁ (le_antisymm (ht.2 1) hi.1)

lemma physicalBlockRegion_indicator_ae (f : (Fin 3 → ℝ) → ℝ) :
    physicalBlockRegion.indicator f=ᵐ[volume]
      (fun y => centralPhysical.indicator f y+
        ∑ i : Fin 3,(physicalEndRegion i).indicator f y) := by
  classical
  filter_upwards [physicalBlockRegion_central_end_exclusive_ae] with y he
  by_cases hc : y∈centralPhysical
  · have hb : y∈physicalBlockRegion := Or.inl hc
    rw [indicator_of_mem hb,indicator_of_mem hc]
    have hsum : (∑ i : Fin 3,(physicalEndRegion i).indicator f y)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (he hc i) _
    rw [hsum,add_zero]
  · rw [indicator_of_notMem hc]
    by_cases hend : ∃ i : Fin 3,y∈physicalEndRegion i
    · obtain ⟨i,hi⟩ := hend
      have hb : y∈physicalBlockRegion := physicalEndRegion_mem_block i hi
      rw [indicator_of_mem hb,zero_add]
      symm
      calc
        _ = (physicalEndRegion i).indicator f y := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            exact indicator_of_notMem (fun hj =>
              disjoint_left.mp (physicalEndRegion_pairwise_disjoint hji) hj hi) _
          · simp
        _ = f y := indicator_of_mem hi f
    · have hb : y∉physicalBlockRegion := by
        rintro (hh|hh)
        · exact hc hh
        · exact hend (mem_iUnion.mp hh)
      rw [indicator_of_notMem hb,zero_add]
      symm
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (fun hi => hend ⟨i,hi⟩) _

end ScalarConductivity

end

end OAI
