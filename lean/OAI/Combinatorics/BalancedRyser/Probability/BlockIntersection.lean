import OAI.Combinatorics.BalancedRyser.Construction.ValidChoice
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Probability.ConfigurationStructure

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem mem_merged_of_on_constituent (M : MergedPairs F)
    (d : Direction F) (s : Bool) {x : Point F}
    (hx : OnLine x (constituent M d s)) : x ∈ mergedPoints M d := by
  simp only [mergedPoints, linePoints, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases s
  · exact Or.inl hx
  · exact Or.inr hx

theorem points_nonempty (C : Configuration F) : C.points.Nonempty := by
  let s : Slot F := (none, false)
  refine ⟨tuplePoint C.merged (C.choice s).tuple 0, ?_⟩
  apply SplitGeometry.selected_designated_mem_points C s
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

theorem pair_common_block (C : Configuration F) (hV : C.Valid) (hC : C.Compatible)
    {x y : Point F} (hx : x ∈ C.points) (hy : y ∈ C.points) :
    ∃ b ∈ C.blockLabels, x ∈ C.blockPoints b ∧ y ∈ C.blockPoints b := by
  classical
  by_cases hs : joiningLine x y ∈ C.splitLines
  · obtain ⟨s, _, hline⟩ := Finset.mem_image.mp hs
    have hxd : x ∈ designated C.merged (C.choice s) := by
      rw [← ConfigurationStructure.split_inter_points C hV hC s]
      refine Finset.mem_inter.mpr ⟨?_, hx⟩
      simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and, hline]
        using onLine_joiningLine_left x y
    have hyd : y ∈ designated C.merged (C.choice s) := by
      rw [← ConfigurationStructure.split_inter_points C hV hC s]
      refine Finset.mem_inter.mpr ⟨?_, hy⟩
      simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and, hline]
        using onLine_joiningLine_right x y
    exact SplitGeometry.selected_pair_common_block C hV s hxd hyd
  · by_cases hm : joiningLine x y ∈ constituentLines C.merged
    · obtain ⟨ds, _, hline⟩ := Finset.mem_image.mp hm
      refine ⟨Sum.inr (Sum.inl ds.1), ?_, ?_, ?_⟩
      · simp [blockLabels, IsBlockLabel]
      · apply Finset.mem_inter.mpr
        refine ⟨mem_merged_of_on_constituent C.merged ds.1 ds.2 ?_, hx⟩
        rw [hline]
        exact onLine_joiningLine_left x y
      · apply Finset.mem_inter.mpr
        refine ⟨mem_merged_of_on_constituent C.merged ds.1 ds.2 ?_, hy⟩
        rw [hline]
        exact onLine_joiningLine_right x y
    · refine ⟨Sum.inl (joiningLine x y), ?_, ?_, ?_⟩
      · simp [blockLabels, IsBlockLabel, hs, hm]
      · apply Finset.mem_inter.mpr
        refine ⟨?_, hx⟩
        simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and]
          using onLine_joiningLine_left x y
      · apply Finset.mem_inter.mpr
        refine ⟨?_, hy⟩
        simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and]
          using onLine_joiningLine_right x y

end Configuration
end Balanced

end OAI
