import Mathlib
import OAI.Geometry.SmoothYau.Estimates.MiddleBox

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory BoxIntegral
open scoped Topology

theorem exists_profile_box_partition (I : Box (Fin 3)) (L : (Fin 3 → ℝ) → ℝ)
    (hL : ContinuousOn L (Box.Icc I)) (hpos : ∀ x ∈ Box.Icc I, 0 < L x) :
    ∃ partition : TaggedPrepartition I, partition.IsPartition ∧
      ∃ ℓ : Box (Fin 3) → ℝ, ∀ J ∈ partition, 0 < ℓ J ∧
        ∀ x ∈ Box.Icc J, ℓ J/2 ≤ L x ∧ L x ≤ ℓ J := by
  classical
  have hr : ∀ x, ∃ r > (0:ℝ), ∀ y ∈ Box.Icc I,
      dist y x ≤ r → x ∈ Box.Icc I → |L y-L x| < L x/3 := by
    intro x
    by_cases hx : x ∈ Box.Icc I
    · obtain ⟨δ,hδ,hδprop⟩ := Metric.continuousWithinAt_iff.mp (hL x hx) (L x/3) (div_pos (hpos x hx) (by norm_num))
      refine ⟨δ/2,by positivity,?_⟩
      intro y hy hyδ _
      have := hδprop hy (lt_of_le_of_lt hyδ (by linarith))
      simpa only [Real.dist_eq] using this
    · exact ⟨1,by norm_num,fun _ _ _ h => (hx h).elim⟩
  choose r hr0 hr using hr
  obtain ⟨partition,hπ,hHen,hsub,-,-⟩ :=
    I.exists_taggedPartition_isHenstock_isSubordinate_homothetic (fun x => ⟨r x,hr0 x⟩)
  refine ⟨partition,hπ,fun J => (4/3:ℝ)*L (partition.tag J),?_⟩
  intro J hJ
  have ht := partition.tag_mem_Icc J
  refine ⟨mul_pos (by norm_num) (hpos _ ht),?_⟩
  intro x hx
  have hxi : x ∈ Box.Icc I := (Box.le_iff_Icc.mp (partition.le_of_mem hJ)) hx
  have hab := hr (partition.tag J) x hxi (hsub J hJ hx) ht
  have hh := abs_lt.mp hab
  constructor <;> linarith

theorem profile_integral_le_partition (I : Box (Fin 3))
    (L : (Fin 3 → ℝ) → ℝ) (hL : ContinuousOn L (Box.Icc I))
    (partition : TaggedPrepartition I) (hπ : partition.IsPartition) (ℓ : Box (Fin 3) → ℝ)
    (hbound : ∀ J ∈ partition, ∀ x ∈ Box.Icc J, L x ≤ ℓ J) :
    (∫ x in Box.Icc I, L x) ≤ ∑ J ∈ partition.boxes, ℓ J*(volume (Box.Ioo J)).toReal := by
  have hi : IntegrableOn L (Box.Icc I) := hL.integrableOn_compact I.isCompact_Icc
  have hpart : (∫ x in Box.Icc I, L x) = ∑ J ∈ partition.boxes, ∫ x in (J : Set (Fin 3 → ℝ)), L x := by
    calc
      (∫ x in Box.Icc I, L x) = ∫ x in (I : Set (Fin 3 → ℝ)), L x :=
        setIntegral_congr_set I.coe_ae_eq_Icc.symm
      _ = ∫ x in partition.toPrepartition.iUnion, L x := by rw [hπ.iUnion_eq]
      _ = _ := integral_biUnion_finset partition.boxes (fun J _ => J.measurableSet_coe)
        partition.pairwiseDisjoint (fun J hJ => hi.mono_set (fun x hx => Box.coe_subset_Icc (partition.le_of_mem hJ hx)))
  rw [hpart]
  refine Finset.sum_le_sum fun J hJ => ?_
  have hJI : (J : Set (Fin 3 → ℝ)) ⊆ Box.Icc I :=
    fun x hx => Box.coe_subset_Icc (partition.le_of_mem hJ hx)
  calc
    (∫ x in (J : Set (Fin 3 → ℝ)), L x) ≤ ∫ _ in (J : Set (Fin 3 → ℝ)), ℓ J := by
      apply setIntegral_mono_on (hi.mono_set hJI) (integrableOn_const (J.measure_coe_lt_top volume).ne) J.measurableSet_coe
      exact fun x hx => hbound J hJ x (Box.coe_subset_Icc hx)
    _ = ℓ J*(volume (Box.Ioo J)).toReal := by
      rw [MeasureTheory.integral_const]
      have he : volume (J : Set (Fin 3 → ℝ)) = volume (Box.Ioo J) :=
        measure_congr (J.coe_ae_eq_Icc.trans J.Ioo_ae_eq_Icc.symm)
      simp [measureReal_def,he,smul_eq_mul,mul_comm]

end

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory BoxIntegral
open scoped Topology

lemma box_profile_integral_pos (I : Box (Fin 3)) (L : (Fin 3 → ℝ) → ℝ)
    (hL : ContinuousOn L (Box.Icc I)) (hL1 : ∀ x ∈ Box.Icc I, 1 ≤ L x) :
    0 < ∫ x in Box.Icc I, L x := by
  have hv : 0 < (volume (Box.Icc I)).toReal := by
    rw [←measure_congr I.coe_ae_eq_Icc,Box.volume_apply']
    exact Finset.prod_pos (fun i _ => sub_pos.mpr (I.lower_lt_upper i))
  have hi := setIntegral_mono_on (integrableOn_const (I.measure_Icc_lt_top volume).ne)
    (hL.integrableOn_compact I.isCompact_Icc) I.measurableSet_Icc hL1
  have he : (∫ _ in Box.Icc I, (1:ℝ)) = (volume (Box.Icc I)).toReal := by simp [measureReal_def]
  rw [he] at hi
  exact hv.trans_le hi

lemma middleBox_partition_mass (I : Box (Fin 3)) (L : (Fin 3 → ℝ) → ℝ)
    (hL : ContinuousOn L (Box.Icc I)) (partition : TaggedPrepartition I)
    (hπ : partition.IsPartition) (ℓ : Box (Fin 3) → ℝ)
    (hbound : ∀ J ∈ partition, ∀ x ∈ Box.Icc J, L x ≤ ℓ J) :
    (∫ x in Box.Icc I, L x)/8 ≤
      ∑ J : {J : Box (Fin 3) // J ∈ partition.boxes}, ℓ J.val*(volume (Box.Icc (middleBox J.val))).toReal := by
  classical
  simp_rw [middleBox_volume,←mul_div_assoc]
  rw [←Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [Finset.sum_coe_sort partition.boxes (fun J => ℓ J*(volume (Box.Ioo J)).toReal)]
  exact profile_integral_le_partition I L hL partition hπ ℓ hbound

lemma box_Ioo_open (I : Box (Fin 3)) : IsOpen (Box.Ioo I) :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

lemma box_Ioo_convex (I : Box (Fin 3)) : Convex ℝ (Box.Ioo I) :=
  convex_pi (fun _ _ => convex_Ioo _ _)

lemma partition_Ioo_disjoint (I : Box (Fin 3)) (partition : TaggedPrepartition I) :
    Pairwise fun A B : {J : Box (Fin 3) // J ∈ partition.boxes} => Disjoint (Box.Ioo A.val) (Box.Ioo B.val) := by
  intro A B hAB
  exact (partition.disjoint_coe_of_mem A.property B.property (fun h => hAB (Subtype.ext h))).mono A.val.Ioo_subset_coe B.val.Ioo_subset_coe

end YauCounterexamples
end

end OAI
