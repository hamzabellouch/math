import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellChainComposition
import OAI.Analysis.RieszRectifiability.Foundations.IndexedSeedChainCounting
import OAI.Analysis.RieszRectifiability.Foundations.SeedMultiplicityIntegration

namespace OAI

/-!
Depth gaps between captured cells are charged to intervening cells. The resulting pointwise
seed-multiplicity bound integrates to a mass estimate for the finite captured family.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem captured_cell_seed_mass_bound {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (F O : Finset (SupportCellDescendant μ R hR k z))
    (seed : SupportCellDescendant μ R hR k z → SupportCellDescendant μ R hR k z) (I : ℕ)
    (hseed : ∀ i ∈ F, i.depth ≤ (seed i).depth ∧ (seed i).depth ≤ i.depth + I ∧
      (seed i).cell ⊆ i.cell)
    (hgap : ∀ i ∈ F, ∀ j ∈ F, (seed i).depth < j.depth → j.cell ⊆ (seed i).cell →
      ∃ t ∈ O, (seed i).depth ≤ t.depth ∧ t.depth < j.depth ∧ j.cell ⊆ t.cell) :
    ∑ i ∈ F, μ (seed i).cell ≤ ((I + 1 : ℕ) : ℝ≥0∞) *
      (μ (cleanSupportCell μ R hR k z) + ∑ t ∈ O, μ t.cell) := by
  classical
  apply measure_sum_le_of_count_multiplicity μ F O (fun i => (seed i).cell) (fun t => t.cell)
    (cleanSupportCell μ R hR k z) (I + 1)
    (fun i _ => cleanSupportCell_measurable μ R hR (k + (seed i).depth)
      ⟨(seed i).center, (seed i).mem_net⟩)
    (fun t _ => cleanSupportCell_measurable μ R hR (k + t.depth) ⟨t.center, t.mem_net⟩)
    (cleanSupportCell_measurable μ R hR k z)
  intro x
  by_cases hx : x ∈ cleanSupportCell μ R hR k z
  · let Pcap := F.filter (fun i => x ∈ (seed i).cell)
    let Ocap := O.filter (fun t => x ∈ t.cell)
    have hmem (i : SupportCellDescendant μ R hR k z) (hi : i ∈ Pcap) :
        i ∈ F ∧ x ∈ (seed i).cell := Finset.mem_filter.mp hi
    have hiparent (i : SupportCellDescendant μ R hR k z) (hi : i ∈ Pcap) : x ∈ i.cell :=
      (hseed i (hmem i hi).1).2.2 (hmem i hi).2
    have hinj : Set.InjOn (fun i : SupportCellDescendant μ R hR k z => i.depth) Pcap := by
      intro i hi j hj hij
      exact i.eq_of_common_point_same_depth j hij x (hiparent i hi) (hiparent j hj)
    have hb := indexed_captured_seed_chain_count Pcap (Ocap.image (fun t => t.depth))
      (fun i => i.depth) (fun i => (seed i).depth) I hinj
      (fun i hi => ⟨(hseed i (hmem i hi).1).1, (hseed i (hmem i hi).1).2.1⟩)
      (by
        intro i hi j hj hdepth
        have hsub := j.cell_nested_of_common_point (seed i) hdepth.le x
          (hiparent j hj) (hmem i hi).2
        obtain ⟨t, ht, hlow, hhigh, hcontain⟩ := hgap i (hmem i hi).1 j (hmem j hj).1 hdepth hsub
        refine ⟨t.depth, Finset.mem_image.mpr ⟨t, ?_, rfl⟩, hlow, hhigh⟩
        exact Finset.mem_filter.mpr ⟨ht, hcontain (hiparent j hj)⟩)
    have hcard : (Ocap.image (fun t => t.depth)).card ≤ Ocap.card := Finset.card_image_le
    have hbound := hb.trans (Nat.mul_le_mul_left (I + 1) (Nat.add_le_add_left hcard 1))
    simpa only [ite_eq_left hx] using! hbound
  · have heq : F.filter (fun i => x ∈ (seed i).cell) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hm := Finset.mem_filter.mp hi
      exact hx (i.cell_subset_top ((hseed i hm.1).2.2 hm.2))
    simp only [heq, Finset.card_empty, Nat.zero_le]

end

end RieszRectifiability

end OAI
