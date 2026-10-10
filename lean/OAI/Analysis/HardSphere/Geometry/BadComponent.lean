import Mathlib
import OAI.Analysis.HardSphere.Geometry.MicroCubeCover

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators Classical
noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice

lemma isBadComponent_iff (B : Set Vertex) (C : Finset Vertex) :
    IsBadComponent B C ↔ C.Nonempty ∧ (↑C : Set Vertex) ⊆ B ∧
      starConnected (↑C) ∧
      ∀ c ∈ C, ∀ x, x ∈ B → starStep c x → x ∈ C := by
  constructor
  · intro hC
    obtain ⟨z, hzB, hz⟩ := hC
    have hzC : z ∈ C := by simpa only [← hz, Finset.mem_coe] using liftedBadComponent_self hzB
    have hC : IsBadComponent B C := ⟨z, hzB, hz⟩
    exact ⟨⟨z, hzC⟩, hC.subset, hC.connected, fun _ hc _ hx hcx ↦ hC.closed hc hx hcx⟩
  · rintro ⟨⟨z, hz⟩, hsub, hconn, hclosed⟩
    refine ⟨z, hsub hz, ?_⟩
    ext w
    constructor
    · intro hw
      exact ⟨hsub hz, hsub hw, withinReach_mono hsub (hconn z hz w hw)⟩
    · intro hw
      exact withinReach_end hz
        (withinReach_invariant (fun _ hu _ hv huv ↦ hclosed _ hu _ hv huv) hz hw.2.2)

lemma finiteBadComponents_iff (B : Set Vertex) :
    FiniteBadComponents B ↔ ∀ z ∈ B, ∃ C : Finset Vertex, IsBadComponent B C ∧ z ∈ C := by
  classical
  constructor
  · intro h z hz
    exact ⟨(h z hz).toFinset, ⟨z, hz, (h z hz).coe_toFinset⟩,
      (h z hz).mem_toFinset.mpr (liftedBadComponent_self hz)⟩
  · intro h z hz
    obtain ⟨C, hC, hzC⟩ := h z hz
    apply C.finite_toSet.subset
    intro w hw
    exact withinReach_end hzC
      (withinReach_invariant (fun _ hu _ hv huv ↦ hC.closed hu hv huv) hzC hw.2.2)

end HardSphere.Lattice

namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma measurable_component_test {n : ℕ} (L : Length) (h r : ℝ) (C : Finset Vertex) :
    Measurable (fun Y : Configuration n L ↦ IsBadComponent (bad h r Y) C) := by
  simp_rw [isBadComponent_iff]
  apply Measurable.and measurable_const
  apply Measurable.and
  · change Measurable (fun Y : Configuration n L ↦ ∀ z, z ∈ C → z ∈ bad h r Y)
    exact Measurable.forall fun z ↦ Measurable.imp measurable_const
      (measurableSet_setOfPred.mp (measurableSet_bad_test L h r z))
  · apply Measurable.and measurable_const
    apply Measurable.forall
    intro c
    apply Measurable.imp measurable_const
    apply Measurable.forall
    intro x
    apply Measurable.imp
    · exact measurableSet_setOfPred.mp (measurableSet_bad_test L h r x)
    · exact Measurable.imp measurable_const measurable_const

lemma measurable_finiteComponents_test {n : ℕ} (L : Length) (h r : ℝ) :
    Measurable (fun Y : Configuration n L ↦ FiniteBadComponents (bad h r Y)) := by
  simp_rw [finiteBadComponents_iff]
  apply Measurable.forall
  intro z
  apply Measurable.imp
  · exact measurableSet_setOfPred.mp (measurableSet_bad_test L h r z)
  · exact Measurable.exists fun C ↦ (measurable_component_test L h r C).and measurable_const

lemma measurable_exceptional {n : ℕ} (L : Length) (h r : ℝ) :
    Measurable (fun Y : Configuration n L ↦ exceptional h r Y) :=
  ((isOpen_allowed n L r).measurableSet.mem.not).or
    (measurable_finiteComponents_test L h r).not

theorem measurableSet_omitted_graph {n : ℕ} (L : Length) (h r : ℝ) :
    MeasurableSet {p : Configuration n L × Torus L | p.2 ∈ omitted h r p.1} := by
  apply Measurable.setOf
  apply Measurable.or ((measurable_exceptional L h r).comp measurable_fst)
  apply Measurable.exists
  intro C
  apply Measurable.and ((measurable_component_test L h r C).comp measurable_fst)
  apply Measurable.exists
  intro z
  exact Measurable.and measurable_const
    (((isCompact_microCube L h z).isClosed.measurableSet.mem).comp measurable_snd)

attribute [local irreducible] omitted

lemma measurableSet_omitted {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) :
    MeasurableSet (omitted h r Y) := by
  have hm : Measurable (fun x : Torus L ↦ (Y, x)) :=
    (measurable_const : Measurable (fun _ : Torus L ↦ Y)).prodMk measurable_id
  exact (measurableSet_omitted_graph (n := n) L h r).preimage hm

lemma measurableSet_retained {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) :
    MeasurableSet (retained h r Y) := (measurableSet_omitted h r Y).compl

theorem measurable_omitted_volume {n : ℕ} (L : Length) (h r : ℝ) :
    Measurable (fun Y : Configuration n L ↦ (volume : Measure (Torus L)) (omitted h r Y)) :=
  measurable_measure_prodMk_left (measurableSet_omitted_graph L h r)

end HardSphere.BathSlice

namespace HardSphere.Lattice

theorem fill_column_meets (C : Finset Vertex) {x : Vertex} (hx : x ∈ fill C)
    (i : Fin 3) : ∃ c ∈ C, ∀ j, j ≠ i → c j = x j := by
  by_contra hn
  apply hx
  apply coordinateRay_exterior C x i 1 (by norm_num)
  intro n hc
  apply hn
  refine ⟨coordinateRay x i 1 n, hc, ?_⟩
  intro j hj
  simp [coordinateRay, hj]

def columnCover (C : Finset Vertex) (i : Fin 3) (lo hi : ℤ) : Finset Vertex :=
  C.biUnion fun c ↦ (Finset.Icc lo hi).image fun k ↦ Function.update c i k

lemma fill_subset_columnCover (C : Finset Vertex) (i : Fin 3) (lo hi : ℤ)
    (hb : ∀ c ∈ C, lo ≤ c i ∧ c i ≤ hi) : fill C ⊆ ↑(columnCover C i lo hi) := by
  intro x hx
  obtain ⟨c, hc, hcol⟩ := fill_column_meets C hx i
  have hbox := fill_subset_coordinateBox C hx i
  obtain ⟨cl, hcl, hclx⟩ := hbox.1
  obtain ⟨cu, hcu, hxcu⟩ := hbox.2
  apply Finset.mem_biUnion.mpr
  refine ⟨c, hc, Finset.mem_image.mpr ⟨x i, Finset.mem_Icc.mpr
    ⟨(hb cl hcl).1.trans hclx, hxcu.trans (hb cu hcu).2⟩, ?_⟩⟩
  ext j
  by_cases hj : j = i
  · subst j; simp
  · simp [Function.update_of_ne hj, hcol j hj]

lemma card_columnCover_le (C : Finset Vertex) (i : Fin 3) (lo hi : ℤ) :
    (columnCover C i lo hi).card ≤ C.card * (hi - lo + 1).toNat := by
  calc
    _ ≤ ∑ c ∈ C, ((Finset.Icc lo hi).image fun k ↦ Function.update c i k).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ C, (Finset.Icc lo hi).card :=
      Finset.sum_le_sum fun c _ ↦ Finset.card_image_le
    _ = _ := by simp [Int.card_Icc, show hi + 1 - lo = hi - lo + 1 by omega]

lemma finite_fill (C : Finset Vertex) : (fill C).Finite := by
  classical
  by_cases hc : C.Nonempty
  · let lo := C.inf' hc (fun c ↦ c 0)
    let hi := C.sup' hc (fun c ↦ c 0)
    exact (columnCover C 0 lo hi).finite_toSet.subset
      (fill_subset_columnCover C 0 lo hi fun c hc ↦
        ⟨Finset.inf'_le (fun c : Vertex ↦ c 0) hc,
          Finset.le_sup' (fun c : Vertex ↦ c 0) hc⟩)
  · have hC : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
    subst C
    have he : fill ∅ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨c, hc, _⟩ := fill_column_meets ∅ hx 0
      exact Finset.notMem_empty c hc
    rw [he]
    exact Set.finite_empty

theorem ncard_fill_le_columns (C : Finset Vertex) (i : Fin 3) (lo hi : ℤ)
    (hb : ∀ c ∈ C, lo ≤ c i ∧ c i ≤ hi) :
    (fill C).ncard ≤ C.card * (hi - lo + 1).toNat := by
  calc
    _ ≤ (↑(columnCover C i lo hi) : Set Vertex).ncard :=
      Set.ncard_le_ncard (fill_subset_columnCover C i lo hi hb)
        (columnCover C i lo hi).finite_toSet
    _ = (columnCover C i lo hi).card := by simp
    _ ≤ _ := card_columnCover_le C i lo hi

end HardSphere.Lattice

end
end
end
end
end

end OAI
