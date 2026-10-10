import Mathlib

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Set Function Filter Topology

variable {ι : Type*} [Fintype ι]

def dyadicBoxPartition (I : Box ι) : ℕ → Prepartition I
  | 0 => ⊤
  | k + 1 => (dyadicBoxPartition I k).biUnion Prepartition.splitCenter

theorem dyadicBoxPartition_isPartition (I : Box ι) (k : ℕ) :
    (dyadicBoxPartition I k).IsPartition := by
  induction k with
  | zero => exact Prepartition.isPartitionTop I
  | succ k ih =>
    exact ih.biUnion (fun J _ => Prepartition.isPartition_splitCenter J)

theorem dyadicBoxPartition_width (I : Box ι) (k : ℕ) (J : Box ι)
    (hJ : J ∈ dyadicBoxPartition I k) (i : ι) :
    J.upper i - J.lower i = (I.upper i - I.lower i) * (1 / 2 : ℝ) ^ k := by
  induction k generalizing J with
  | zero =>
    have h : J = I := Prepartition.mem_top.mp hJ
    subst J
    simp
  | succ k ih =>
    obtain ⟨P, hP, hJP⟩ := (dyadicBoxPartition I k).mem_biUnion.mp hJ
    rw [Prepartition.upper_sub_lower_of_mem_splitCenter hJP, ih P hP, pow_succ]
    ring

theorem dyadicBoxPartition_volume (I : Box ι) (k : ℕ) (J : Box ι)
    (hJ : J ∈ dyadicBoxPartition I k) :
    (volume : Measure (ι → ℝ)).real J =
      (volume : Measure (ι → ℝ)).real I * ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι := by
  simp only [Measure.real, Box.volume_apply']
  simp_rw [dyadicBoxPartition_width I k J hJ]
  rw [Finset.prod_mul_distrib]
  simp

theorem box_volume_real_pos (I : Box ι) :
    0 < (volume : Measure (ι → ℝ)).real I := by
  rw [Measure.real, Box.volume_apply']
  exact Finset.prod_pos (fun i _ => sub_pos.mpr (I.lower_lt_upper i))

def boxWidthBound (I : Box ι) : ℝ := ∑ i, (I.upper i - I.lower i)

theorem boxWidthBound_nonneg (I : Box ι) : 0 ≤ boxWidthBound I :=
  Finset.sum_nonneg (fun i _ => (sub_pos.mpr (I.lower_lt_upper i)).le)

theorem box_width_le_bound (I : Box ι) (i : ι) :
    I.upper i - I.lower i ≤ boxWidthBound I := by
  classical
  exact Finset.single_le_sum (fun j _ => (sub_pos.mpr (I.lower_lt_upper j)).le)
    (Finset.mem_univ i)

theorem dyadicBoxPartition_dist_upper_le (I : Box ι) (k : ℕ) (J : Box ι)
    (hJ : J ∈ dyadicBoxPartition I k) (x : ι → ℝ) (hx : x ∈ J) :
    dist x J.upper ≤ boxWidthBound I * (1 / 2 : ℝ) ^ k := by
  have hp : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
  apply (dist_pi_le_iff (mul_nonneg (boxWidthBound_nonneg I) hp)).mpr
  intro i
  have hi := hx i
  calc
    dist (x i) (J.upper i) = J.upper i - x i := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hi.2)]
      ring
    _ ≤ J.upper i - J.lower i := by linarith [hi.1]
    _ = (I.upper i - I.lower i) * (1 / 2 : ℝ) ^ k :=
      dyadicBoxPartition_width I k J hJ i
    _ ≤ boxWidthBound I * (1 / 2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right (box_width_le_bound I i) hp

theorem box_frontier_volume_zero (I : Box ι) :
    (volume : Measure (ι → ℝ)) (frontier (I : Set (ι → ℝ))) = 0 := by
  have hopen : IsOpen (Box.Ioo I) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hsub : frontier (I : Set (ι → ℝ)) ⊆ Box.Icc I \ Box.Ioo I := by
    intro x hx
    exact ⟨closure_minimal Box.coe_subset_Icc I.isCompact_Icc.isClosed hx.1,
      fun hi => hx.2 (hopen.subset_interior_iff.mpr I.Ioo_subset_coe hi)⟩
  have heq : (Box.Icc I \ Box.Ioo I) =ᵐ[volume] (∅ : Set (ι → ℝ)) := by
    filter_upwards [I.Ioo_ae_eq_Icc] with x hx
    apply propext
    change (x ∈ Box.Icc I ∧ x ∉ Box.Ioo I) ↔ False
    have hx' : x ∈ Box.Ioo I ↔ x ∈ Box.Icc I := iff_of_eq hx
    tauto
  exact measure_mono_null hsub ((measure_congr heq).trans measure_empty)

theorem dyadic_box_scale_tendsto_zero :
    Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

def DyadicBoxIndex (I : Box ι) (k : ℕ) := ↥(dyadicBoxPartition I k).boxes

instance (I : Box ι) (k : ℕ) : Fintype (DyadicBoxIndex I k) := by
  classical
  unfold DyadicBoxIndex
  infer_instance

def dyadicBoxCell (I : Box ι) (k : ℕ) (J : DyadicBoxIndex I k) : Set (ι → ℝ) :=
  (J.val : Set (ι → ℝ))

theorem dyadicBoxCell_measurable (I : Box ι) (k : ℕ) (J : DyadicBoxIndex I k) :
    MeasurableSet (dyadicBoxCell I k J) := J.val.measurableSet_coe

theorem dyadicBoxCell_disjoint (I : Box ι) (k : ℕ) :
    Pairwise (Disjoint on dyadicBoxCell I k) := by
  intro J P hne
  exact (dyadicBoxPartition I k).pairwiseDisjoint J.property P.property
    (fun h => hne (Subtype.ext h))

theorem dyadicBoxCell_cover (I : Box ι) (k : ℕ) :
    (⋃ J : DyadicBoxIndex I k, dyadicBoxCell I k J) = (I : Set (ι → ℝ)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨J, hx⟩ := mem_iUnion.mp hx
    exact (dyadicBoxPartition I k).le_of_mem J.property hx
  · intro hx
    obtain ⟨J, hJ, hxJ⟩ := dyadicBoxPartition_isPartition I k x hx
    exact mem_iUnion.mpr ⟨⟨J, hJ⟩, hxJ⟩

end

end RieszRectifiability

end OAI
