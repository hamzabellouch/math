import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CentralPhysicalRegion

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma centralPhysical_subset_ball {y : Fin 3 → ℝ} (hy : y∈centralPhysical) :
    WithLp.toLp 2 y∈ball := by
  have hp := (centralParent_time_iff y).mp ((centralPhysical_time_iff y).mp hy).1
  have ho : WithLp.toLp 2 y∈sourceOuterBox := by
    change |y 0| ≤ sourceLength ∧ |y 1| ≤ 1 ∧ |y 2| ≤ 1
    rcases hp with ⟨⟨hx,hy,_⟩,hz⟩
    dsimp [sourcePairCoordinates] at hx hy
    norm_num [centralOuterX,centralOuterY,centralHeight,sourceLength,sourceRadialWidth,
      sourceHole,centralThickness] at hx hy hz ⊢
    exact ⟨by linarith,by linarith,by linarith⟩
  have hn := sourceBox_norm_bound ho
  simpa only [ball,Metric.mem_ball,dist_zero_right] using
    hn.trans (by norm_num : (5:ℝ)/2<3)

lemma centralPhysical_mem_interior_of_strict {y : Fin 3 → ℝ}
    (hp : centralThickness<sourceCollarTime y)
    (hc : ∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)< -centralThickness) :
    y∈interior centralPhysical := by
  have ht := locallyLipschitz_sourceCollarTime.continuous
  have hp' : ∀ᶠ z in 𝓝 y,centralThickness<sourceCollarTime z :=
    ht.continuousAt (Ioi_mem_nhds hp)
  have hc' (k : Fin 2) : ∀ᶠ z in 𝓝 y,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm z)< -centralThickness :=
    (ht.comp (sourceChildHomeomorph (actualChildSign k)).symm.continuous).continuousAt (Iio_mem_nhds (hc k))
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hp',eventually_all.mpr hc'] with z hpz hcz
  exact (centralPhysical_time_iff z).mpr ⟨hpz.le,fun k => (hcz k).le⟩

def centralJoinOpen (i : Fin 4) : Set (Fin 3 → ℝ) :=
  ![interior centralPhysical,
    sourceCollarTime ⁻¹' Ioo 0 (2*centralThickness),
    (fun y => sourceCollarTime ((sourceChildHomeomorph 1).symm y)) ⁻¹' Ioo (-2*centralThickness) 0,
    (fun y => sourceCollarTime ((sourceChildHomeomorph (-1)).symm y)) ⁻¹' Ioo (-2*centralThickness) 0] i

lemma centralJoinOpen_isOpen (i : Fin 4) : IsOpen (centralJoinOpen i) := by
  have ht := locallyLipschitz_sourceCollarTime.continuous
  fin_cases i
  · exact isOpen_interior
  · exact isOpen_Ioo.preimage ht
  · exact isOpen_Ioo.preimage (ht.comp (sourceChildHomeomorph 1).symm.continuous)
  · exact isOpen_Ioo.preimage (ht.comp (sourceChildHomeomorph (-1)).symm.continuous)

lemma centralJoinOpen_covers : centralPhysical⊆⋃ i,centralJoinOpen i := by
  intro y hy
  obtain ⟨hp,hc⟩ := (centralPhysical_time_iff y).mp hy
  by_cases hpe : sourceCollarTime y=centralThickness
  · apply mem_iUnion.mpr
    refine ⟨1,?_⟩
    change sourceCollarTime y∈Ioo 0 (2*centralThickness)
    rw [hpe]
    norm_num [centralThickness]
  by_cases hce : ∃ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)= -centralThickness
  · obtain ⟨k,hk⟩ := hce
    apply mem_iUnion.mpr
    fin_cases k
    · refine ⟨2,?_⟩
      change sourceCollarTime ((sourceChildHomeomorph 1).symm y)∈Ioo (-2*centralThickness) 0
      norm_num [actualChildSign] at hk
      rw [hk]
      norm_num [centralThickness]
    · refine ⟨3,?_⟩
      change sourceCollarTime ((sourceChildHomeomorph (-1)).symm y)∈Ioo (-2*centralThickness) 0
      norm_num [actualChildSign] at hk
      rw [hk]
      norm_num [centralThickness]
  · exact mem_iUnion.mpr ⟨0,centralPhysical_mem_interior_of_strict
      (lt_of_le_of_ne hp (Ne.symm hpe)) (fun k => lt_of_le_of_ne (hc k) (fun he => hce ⟨k,he⟩))⟩

theorem exists_centralJoinPartition :
    ∃ ρ : SmoothPartitionOfUnity (Fin 4) (modelWithCornersSelf ℝ (Fin 3 → ℝ))
        (Fin 3 → ℝ) centralPhysical,ρ.IsSubordinate centralJoinOpen :=
  SmoothPartitionOfUnity.exists_isSubordinate _ centralPhysical_compact.isClosed
    centralJoinOpen centralJoinOpen_isOpen centralJoinOpen_covers

theorem exists_centralJoinPartition_neighborhood :
    ∃ ρ : SmoothPartitionOfUnity (Fin 4) (modelWithCornersSelf ℝ (Fin 3 → ℝ))
        (Fin 3 → ℝ) centralPhysical,ρ.IsSubordinate centralJoinOpen ∧
      ∀ y∈centralPhysical,(fun z => ∑ i : Fin 4,ρ i z)=ᶠ[𝓝 y] (fun _ => (1:ℝ)) := by
  obtain ⟨K,hK,hKc,hCK,hKU⟩ := exists_compact_closed_between centralPhysical_compact
    (isOpen_iUnion centralJoinOpen_isOpen) centralJoinOpen_covers
  obtain ⟨g,hg⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Fin 3 → ℝ)) hKc centralJoinOpen centralJoinOpen_isOpen hKU
  let ρ : SmoothPartitionOfUnity (Fin 4) (modelWithCornersSelf ℝ (Fin 3 → ℝ))
      (Fin 3 → ℝ) centralPhysical :=
    { toFun := g.toFun
      locallyFinite' := g.locallyFinite'
      nonneg' := g.nonneg'
      sum_eq_one' := fun y hy => g.sum_eq_one (interior_subset (hCK hy))
      sum_le_one' := g.sum_le_one' }
  refine ⟨ρ,hg,fun y hy => ?_⟩
  filter_upwards [mem_interior_iff_mem_nhds.mp (hCK hy)] with z hz
  change ∑ i : Fin 4,g i z=1
  simpa only [finsum_eq_sum_of_fintype] using g.sum_eq_one hz

def centralJoinPartition : SmoothPartitionOfUnity (Fin 4)
    (modelWithCornersSelf ℝ (Fin 3 → ℝ)) (Fin 3 → ℝ) centralPhysical :=
  Classical.choose exists_centralJoinPartition_neighborhood

lemma centralJoinPartition_subordinate : centralJoinPartition.IsSubordinate centralJoinOpen :=
  (Classical.choose_spec exists_centralJoinPartition_neighborhood).1

lemma centralJoinPartition_eventually_sum {y : Fin 3 → ℝ} (hy : y∈centralPhysical) :
    (fun z => ∑ i : Fin 4,centralJoinPartition i z)=ᶠ[𝓝 y] (fun _ => (1:ℝ)) :=
  (Classical.choose_spec exists_centralJoinPartition_neighborhood).2 y hy

lemma centralJoinPartition_smooth (i : Fin 4) : ContDiff ℝ (↑(⊤:ℕ∞)) (centralJoinPartition i) :=
  (centralJoinPartition i).contMDiff.contDiff

lemma centralJoinPartition_bound (i : Fin 4) (y : Fin 3 → ℝ) : |centralJoinPartition i y| ≤ 1 := by
  rw [abs_of_nonneg (centralJoinPartition.nonneg i y)]
  exact centralJoinPartition.le_one i y

lemma centralJoinPartition_interior_support : tsupport (centralJoinPartition 0)⊆centralPhysical :=
  (centralJoinPartition_subordinate 0).trans interior_subset

lemma centralJoinPartition_interior_compact : HasCompactSupport (centralJoinPartition 0) :=
  centralPhysical_compact.of_isClosed_subset (isClosed_tsupport _) centralJoinPartition_interior_support

lemma centralJoinPartition_parent_support :
    tsupport (centralJoinPartition 1)⊆sourceClosedCollarBand 0 (2*centralThickness) := by
  intro y hy
  have ht := centralJoinPartition_subordinate 1 hy
  change sourceCollarTime y∈Ioo 0 (2*centralThickness) at ht
  exact ⟨ht.1.le,ht.2.le⟩

lemma centralJoinPartition_parent_compact : HasCompactSupport (centralJoinPartition 1) :=
  (isCompact_sourceClosedCollarBand (by norm_num) (by norm_num [centralThickness])).of_isClosed_subset
    (isClosed_tsupport _) centralJoinPartition_parent_support

def centralChildPatch (k : Fin 2) : Fin 4 := ⟨k.val+2,by omega⟩

def centralJoinChildCutoff (k : Fin 2) (y : Fin 3 → ℝ) : ℝ :=
  centralJoinPartition (centralChildPatch k) (sourceChildCoordinates (actualChildSign k) y)

lemma centralJoinChildCutoff_smooth (k : Fin 2) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (centralJoinChildCutoff k) :=
  (centralJoinPartition_smooth _).comp (sourceChildCoordinates_contDiff _)

lemma centralJoinChildCutoff_bound (k : Fin 2) (y : Fin 3 → ℝ) : |centralJoinChildCutoff k y| ≤ 1 :=
  centralJoinPartition_bound _ _

lemma centralJoinChildCutoff_support (k : Fin 2) :
    tsupport (centralJoinChildCutoff k)⊆sourceClosedCollarBand (-2*centralThickness) 0 := by
  intro y hy
  have ht : sourceChildCoordinates (actualChildSign k) y∈tsupport (centralJoinPartition (centralChildPatch k)) :=
    tsupport_comp_subset_preimage (centralJoinPartition (centralChildPatch k))
      (sourceChildCoordinates_contDiff _).continuous hy
  have hp := centralJoinPartition_subordinate (centralChildPatch k) ht
  have he : centralJoinOpen (centralChildPatch k)=
      (fun z => sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm z)) ⁻¹' Ioo (-2*centralThickness) 0 := by
    fin_cases k <;> norm_num [centralJoinOpen,centralChildPatch,actualChildSign]
  rw [he] at hp
  change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm
    ((sourceChildHomeomorph (actualChildSign k)) y))∈Ioo (-2*centralThickness) 0 at hp
  rw [Homeomorph.symm_apply_apply] at hp
  exact ⟨hp.1.le,hp.2.le⟩

lemma centralJoinChildCutoff_compact (k : Fin 2) : HasCompactSupport (centralJoinChildCutoff k) :=
  (isCompact_sourceClosedCollarBand (by norm_num [centralThickness]) (by norm_num)).of_isClosed_subset
    (isClosed_tsupport _) (centralJoinChildCutoff_support k)

lemma centralJoinPartition_sum {y : Fin 3 → ℝ} (hy : y∈centralPhysical) :
    ∑ i : Fin 4,centralJoinPartition i y=1 := by
  simpa only [finsum_eq_sum_of_fintype] using centralJoinPartition.sum_eq_one hy

lemma centralJoinPartition_derivative_sum {y : Fin 3 → ℝ} (hy : y∈interior centralPhysical)
    (j : Fin 3) : ∑ i : Fin 4,fderiv ℝ (centralJoinPartition i) y (Pi.single j 1)=0 := by
  have he : (fun z => ∑ i : Fin 4,centralJoinPartition i z)=ᶠ[𝓝 y] (fun _ => (1:ℝ)) := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hy] with z hz
    exact centralJoinPartition_sum hz
  have hd := Filter.EventuallyEq.fderiv_eq he (𝕜:=ℝ)
  rw [fderiv_fun_sum (fun i _ => (centralJoinPartition_smooth i).differentiable (by simp) y)] at hd
  have h := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) hd
  simpa using h

end ScalarConductivity

end

end OAI
