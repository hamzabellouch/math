import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonGrid

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonGridComparison
open Classical Set MeasureTheory Metric
namespace PolygonGrid

instance : IsLocallyFiniteMeasure (Measure.count : Measure ℕ) where
  finiteAtNhds n := ⟨{n}, (isOpen_discrete _).mem_nhds rfl, by simp⟩

instance : IsLocallyFiniteMeasure μ := by
  unfold μ
  infer_instance

instance : Measure.OuterRegular μ := by
  unfold μ
  infer_instance

instance : Measure.InnerRegularCompactLTTop μ := by
  unfold μ
  infer_instance

@[simp] theorem volume_region (m : ℕ) : μ (region m)=m := by
  have he : {i : ℕ | i < m}=(Finset.range m : Set ℕ) := by ext i; simp
  simp only [μ,region,Measure.prod_prod,he,Measure.count_apply_finset,Finset.card_range]
  simp

theorem compact_closure {m : ℕ} {S : Set PlaneTracks} (hS : S⊆region m) : IsCompact (closure S) := by
  let K : Set PlaneTracks := (Finset.range m : Set ℕ) ×ˢ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1
  have hK : IsCompact K := (Finset.finite_toSet _).isCompact.prod (isCompact_Icc.prod isCompact_Icc)
  apply hK.of_isClosed_subset isClosed_closure
  apply hK.isClosed.closure_subset_iff.mpr
  intro p hp
  have h := hS hp
  exact ⟨by simpa using h.1,⟨h.2.1.1,h.2.1.2.le⟩,⟨h.2.2.1,h.2.2.2.le⟩⟩

theorem strict_grid_comparison {m : ℕ} {S T : Set PlaneTracks}
    (hS : S⊆region m) (hT : T⊆region m)
    (hμ : μ (closure S) < μ (interior T)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ε : ℝ, 0 < ε → ε < δ →
      ∃ (N : ℕ) (I J : Finset (Index m N)), Nonempty (I ↪ J) ∧
        S⊆⋃i∈I,cell ε i ∧ ∀j∈J,cell ε j⊆T := by
  obtain ⟨r,hrS,hrT⟩ := exists_between hμ
  obtain ⟨O,hSO,hO,hOr⟩ := (closure S).exists_isOpen_lt_of_lt r hrS
  have hfinite : μ (interior T)≠⊤ := by
    apply ne_top_of_le_ne_top (by simp : μ (region m)≠⊤)
    exact measure_mono (Set.Subset.trans interior_subset hT)
  obtain ⟨K,hKT,hK,hrK⟩ := isOpen_interior.measurableSet.exists_lt_isCompact_of_ne_top hfinite hrT
  obtain ⟨δS,hδS,hOS⟩ := (compact_closure hS).exists_thickening_subset_open hO hSO
  obtain ⟨δK,hδK,hTK⟩ := hK.exists_thickening_subset_open isOpen_interior hKT
  refine ⟨min δS δK,lt_min hδS hδK,fun ε hε hδ => ?_⟩
  let N : ℕ := ⌈1/ε⌉₊+1
  have hN : 1/ε < (N:ℝ) := by
    have h := Nat.le_ceil (1/ε)
    dsimp [N]
    simp only [Nat.cast_add,Nat.cast_one]
    linarith
  let hits (A : Set PlaneTracks) : Finset (Index m N) := Finset.univ.filter (fun i => (cell ε i∩A).Nonempty)
  have cover (A : Set PlaneTracks) (hA : A⊆region m) : A⊆⋃i∈hits A,cell ε i := by
    intro p hp
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (region_covered hε hN (hA hp))
    exact Set.mem_iUnion₂.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hi,hp⟩,hi⟩
  have inO : (⋃i∈hits S,cell ε i)⊆O := by
    intro p hp
    obtain ⟨i,hi,hp⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨q,hq,hqS⟩ := (Finset.mem_filter.mp hi).2
    apply hOS
    rw [mem_thickening_iff]
    exact ⟨q,subset_closure hqS,(cell_dist hε hp hq).trans (hδ.trans_le (min_le_left _ _))⟩
  have inT : ∀j∈hits K,cell ε j⊆T := by
    intro j hj p hp
    obtain ⟨q,hq,hqK⟩ := (Finset.mem_filter.mp hj).2
    apply interior_subset
    apply hTK
    rw [mem_thickening_iff]
    exact ⟨q,hqK,(cell_dist hε hp hq).trans (hδ.trans_le (min_le_right _ _))⟩
  have hKregion : K⊆region m := Set.Subset.trans hKT (Set.Subset.trans interior_subset hT)
  have hmass : μ (⋃i∈hits S,cell ε i) < μ (⋃j∈hits K,cell ε j) :=
    lt_of_le_of_lt (measure_mono inO) ((hOr.trans hrK).trans_le (measure_mono (cover K hKregion)))
  exact ⟨N,hits S,hits K,matching_of_volume hε _ _ hmass,cover S hS,inT⟩

end PolygonGrid
end PolygonGridComparison

end SimpleAmenable
end
end

end OAI
