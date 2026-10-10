import OAI.GroupTheory.Thompson.BasicIntervalNesting
import Mathlib.Data.Finset.Preimage
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-!
# Finite partitions into basic dyadic intervals

Closed cells cover the unit interval; their open interiors are disjoint.
Restriction is the actual inverse image of the cell set under affine insertion.
-/

noncomputable section

namespace ThompsonNonamenability

open Set

structure BasicPartition where
  cells : Finset BasicInterval
  cover : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ I ∈ cells, x ∈ I.carrier
  disjoint : (cells : Set BasicInterval).Pairwise
    (fun I J => Disjoint I.interior J.interior)

namespace BasicPartition

@[ext]
theorem ext {T U : BasicPartition} (h : T.cells = U.cells) : T = U := by
  cases T
  cases U
  cases h
  rfl

def cellCount (T : BasicPartition) : ℕ := T.cells.card

/-- The interval is exactly covered by partition cells contained in it. -/
def Respects (T : BasicPartition) (I : BasicInterval) : Prop :=
  ∀ x ∈ I.carrier, ∃ K ∈ T.cells, K.Contained I ∧ x ∈ K.carrier

theorem cellCount_pos (T : BasicPartition) : 0 < T.cellCount := by
  obtain ⟨I, hI, _⟩ := T.cover 0 ⟨le_rfl, zero_le_one⟩
  exact Finset.card_pos.mpr ⟨I, hI⟩

theorem respects_of_mem (T : BasicPartition) {I : BasicInterval}
    (hI : I ∈ T.cells) : T.Respects I := by
  intro x hx
  exact ⟨I, hI, I.contained_refl, hx⟩

private theorem interiors_overlap_of_mem_interior_mem_carrier
    {I J : BasicInterval} {x : ℝ} (hxI : x ∈ I.interior)
    (hxJ : x ∈ J.carrier) : (I.interior ∩ J.interior).Nonempty := by
  have h : max I.left J.left < min I.right J.right := by
    apply lt_min
    · exact max_lt I.left_lt_right (lt_of_le_of_lt hxJ.1 hxI.2)
    · exact max_lt (lt_of_lt_of_le hxI.1 hxJ.2) J.left_lt_right
  obtain ⟨y, hy₁, hy₂⟩ := exists_between h
  exact ⟨y, ⟨lt_of_le_of_lt (le_max_left _ _) hy₁,
    lt_of_lt_of_le hy₂ (min_le_left _ _)⟩,
    ⟨lt_of_le_of_lt (le_max_right _ _) hy₁,
    lt_of_lt_of_le hy₂ (min_le_right _ _)⟩⟩

/-- At an interior point, even membership in another closed cell forces equality. -/
theorem eq_of_mem_interior_mem_carrier (T : BasicPartition)
    {I J : BasicInterval} (hI : I ∈ T.cells) (hJ : J ∈ T.cells)
    {x : ℝ} (hxI : x ∈ I.interior) (hxJ : x ∈ J.carrier) : I = J := by
  by_contra hne
  obtain ⟨y, hyI, hyJ⟩ := interiors_overlap_of_mem_interior_mem_carrier hxI hxJ
  exact Set.disjoint_left.mp (T.disjoint hI hJ hne) hyI hyJ

/-- Equivalent geometric crossing condition, including the endpoint argument. -/
theorem respects_iff (T : BasicPartition) (I : BasicInterval) :
    T.Respects I ↔ ∀ K ∈ T.cells,
      (K.interior ∩ I.interior).Nonempty → K.Contained I := by
  constructor
  · intro h K hK ⟨x, hxK, hxI⟩
    obtain ⟨L, hL, hLI, hxL⟩ := h x ⟨hxI.1.le, hxI.2.le⟩
    exact (T.eq_of_mem_interior_mem_carrier hK hL hxK hxL).symm ▸ hLI
  · intro h
    classical
    let contained := T.cells.filter (fun K => K.Contained I)
    let covered : Set ℝ := ⋃ K ∈ contained, K.carrier
    have hclosed : IsClosed covered := by
      apply isClosed_biUnion_finset
      intro K hK
      exact isClosed_Icc
    have hinterior : I.interior ⊆ covered := by
      intro x hxI
      have hxunit : x ∈ Set.Icc (0 : ℝ) 1 :=
        I.carrier_subset_unit ⟨hxI.1.le, hxI.2.le⟩
      obtain ⟨K, hK, hxK⟩ := T.cover x hxunit
      have hmeet : (K.interior ∩ I.interior).Nonempty := by
        obtain ⟨y, hyI, hyK⟩ :=
          interiors_overlap_of_mem_interior_mem_carrier hxI hxK
        exact ⟨y, hyK, hyI⟩
      have hKI := h K hK hmeet
      exact Set.mem_iUnion₂.mpr ⟨K, Finset.mem_filter.mpr ⟨hK, hKI⟩, hxK⟩
    have hcarrier : I.carrier ⊆ covered := by
      have hc := closure_minimal hinterior hclosed
      simpa only [BasicInterval.interior, BasicInterval.carrier,
        closure_Ioo I.left_lt_right.ne] using hc
    intro x hx
    obtain ⟨K, hK, hxK⟩ := Set.mem_iUnion₂.mp (hcarrier hx)
    exact ⟨K, (Finset.mem_filter.mp hK).1, (Finset.mem_filter.mp hK).2, hxK⟩

/-- A sufficiently fine actual partition respects the specified basic interval. -/
theorem respects_of_mesh_lt (T : BasicPartition) (I : BasicInterval)
    (hmesh : ∀ K ∈ T.cells, K.length < I.length) : T.Respects I := by
  apply (T.respects_iff I).mpr
  intro K hK hmeet
  rcases BasicInterval.overlap_interior_nested hmeet with hKI | hIK
  · exact hKI
  · have hlen : I.length ≤ K.length := by
      rw [I.length_eq_right_sub_left, K.length_eq_right_sub_left]
      exact sub_le_sub hIK.2 hIK.1
    exact False.elim (not_lt_of_ge hlen (hmesh K hK))

/-- Affinely normalized cells. Membership is exactly membership after insertion. -/
def restrictCells (T : BasicPartition) (I : BasicInterval) : Finset BasicInterval :=
  T.cells.preimage I.comp I.comp_left_injective.injOn

@[simp]
theorem mem_restrictCells (T : BasicPartition) (I J : BasicInterval) :
    J ∈ T.restrictCells I ↔ I.comp J ∈ T.cells :=
  Finset.mem_preimage

/-- The genuine partition obtained by restriction and affine normalization. -/
def restrict (T : BasicPartition) (I : BasicInterval) (h : T.Respects I) :
    BasicPartition where
  cells := T.restrictCells I
  cover := by
    intro x hx
    have hchart : I.chart x ∈ I.carrier :=
      (I.chart_mem_self_carrier_iff x).mpr hx
    obtain ⟨K, hK, hKI, hxK⟩ := h (I.chart x) hchart
    obtain ⟨J, hJ⟩ := BasicInterval.contained_iff_exists_comp.mp hKI
    refine ⟨J, (T.mem_restrictCells I J).mpr (hJ.symm ▸ hK), ?_⟩
    apply (I.chart_mem_carrier_iff J x).mp
    simpa only [hJ] using hxK
  disjoint := by
    intro J hJ K hK hne
    apply Set.disjoint_left.mpr
    intro x hxJ hxK
    have hJK : I.comp J ≠ I.comp K := fun heq => hne (I.comp_left_injective heq)
    exact Set.disjoint_left.mp
      (T.disjoint ((T.mem_restrictCells I J).mp hJ)
        ((T.mem_restrictCells I K).mp hK) hJK)
      ((I.chart_mem_interior_iff J x).mpr hxJ)
      ((I.chart_mem_interior_iff K x).mpr hxK)

@[simp]
theorem mem_restrict_cells (T : BasicPartition) (I : BasicInterval)
    (h : T.Respects I) (J : BasicInterval) :
    J ∈ (T.restrict I h).cells ↔ I.comp J ∈ T.cells :=
  T.mem_restrictCells I J

theorem restrict_proof_irrel (T : BasicPartition) (I : BasicInterval)
    (h h' : T.Respects I) : T.restrict I h = T.restrict I h' := rfl

open Classical in
theorem restrict_cellCount_eq_filter_card (T : BasicPartition) (I : BasicInterval)
    (h : T.Respects I) :
    (T.restrict I h).cellCount = (T.cells.filter (fun K => K.Contained I)).card := by
  classical
  change (T.cells.preimage I.comp I.comp_left_injective.injOn).card = _
  rw [Finset.card_preimage]
  congr 1
  ext K
  simp only [Finset.mem_filter, Set.mem_range,
    ← BasicInterval.contained_iff_exists_comp]

theorem restrict_cellCount_lt (T : BasicPartition) (I : BasicInterval)
    (h : T.Respects I) (hI : I.Internal) :
    (T.restrict I h).cellCount < T.cellCount := by
  classical
  rw [T.restrict_cellCount_eq_filter_card I h]
  obtain ⟨K, hK, hxK⟩ := T.cover 0 ⟨le_rfl, zero_le_one⟩
  have hnot : ¬K.Contained I := by
    intro hKI
    have hle : I.left ≤ 0 := le_trans hKI.1 hxK.1
    exact (not_le_of_gt hI.1) hle
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have hf : K ∈ T.cells.filter (fun K => K.Contained I) := heq.symm ▸ hK
  exact hnot (Finset.mem_filter.mp hf).2

theorem restrict_respects (T : BasicPartition) (I J : BasicInterval)
    (hI : T.Respects I) (hIJ : T.Respects (I.comp J)) :
    (T.restrict I hI).Respects J := by
  intro x hx
  have hchart : I.chart x ∈ (I.comp J).carrier :=
    (I.chart_mem_carrier_iff J x).mpr hx
  obtain ⟨K, hK, hKIJ, hxK⟩ := hIJ (I.chart x) hchart
  have hKI : K.Contained I :=
    ⟨le_trans (I.comp_contained J).1 hKIJ.1,
      le_trans hKIJ.2 (I.comp_contained J).2⟩
  obtain ⟨L, hL⟩ := BasicInterval.contained_iff_exists_comp.mp hKI
  refine ⟨L, (T.mem_restrict_cells I hI L).mpr (hL.symm ▸ hK), ?_, ?_⟩
  · apply (I.comp_contained_iff L J).mp
    simpa only [hL] using hKIJ
  · apply (I.chart_mem_carrier_iff L x).mp
    simpa only [hL] using hxK

theorem restrict_restrict (T : BasicPartition) (I J : BasicInterval)
    (hI : T.Respects I) (hIJ : T.Respects (I.comp J)) :
    (T.restrict I hI).restrict J (T.restrict_respects I J hI hIJ) =
      T.restrict (I.comp J) hIJ := by
  apply BasicPartition.ext
  ext K
  simp only [mem_restrict_cells, BasicInterval.comp_assoc]

end BasicPartition

end ThompsonNonamenability

end

end OAI
