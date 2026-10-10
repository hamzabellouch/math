import OAI.Combinatorics.BalancedRyser.Construction.ParallelCoverObstruction
import OAI.Combinatorics.BalancedRyser.Construction.TwoSplitCoverObstruction
import OAI.Combinatorics.BalancedRyser.Incidence.ForcedSinglePencil
import OAI.Combinatorics.BalancedRyser.Incidence.ParallelPencilForcing
import OAI.Combinatorics.BalancedRyser.Probability.ForcedNonsplitLabels

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem nonsplit_pencil_trace_subset_partner
    (hvalid : C.Valid) (hcompat : C.Compatible)
    (p : Point F) (hb : 2 ≤ C.splitMultiplicity p)
    (A : Finset (BlockLabel F)) (hlabels : ∀ b ∈ A, C.IsBlockLabel b)
    (hthrough : ∀ b ∈ A, C.NonsplitThrough p b) :
    C.designatedAt p ∩ A.biUnion C.blockPoints ⊆ C.partnerSet p := by
  intro x hx
  obtain ⟨hxd, hxb⟩ := Finset.mem_inter.mp hx
  obtain ⟨b, hbA, hxb⟩ := Finset.mem_biUnion.mp hxb
  have hbt := hthrough b hbA
  rcases b with l | d | s
  · exact False.elim (Finset.disjoint_left.mp
      (ConstructionPartners.regular_block_disjoint_designatedAt C hvalid hcompat p hb l
        (hlabels (Sum.inl l) hbA) hbt) hxb hxd)
  · obtain ⟨side, hp⟩ := hbt
    exact ConstructionPartners.merged_block_inter_designatedAt_subset_partnerSet
      C hvalid hcompat p hb d side hp (Finset.mem_inter.mpr ⟨hxb, hxd⟩)
  · exact False.elim hbt

theorem affine_pencil_cover_impossible_of_budget
    (hvalid : C.Valid) (hcompat : C.Compatible)
    {rho : ℝ} {cap : ℕ} (hocc : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (hlocal : C.LocalCondition)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcard : B.card ≤ Fintype.card F) (p : Point F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) ≤
      rho * Fintype.card F / 4) :
    ¬ ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b := by
  intro hcover
  have hsubset := C.forcedNonsplitLabels_subset hvalid hocc hsize B hlabels hcover p hbudget
  have hbpos := (C.remaining_labels_budget B p hsubset hcard).1
  by_cases hb1 : C.splitMultiplicity p = 1
  · exact C.one_split_impossible_of_pencil_budget hvalid hocc hsize B hlabels hcard hcover p hbudget hb1
  have hbge : 2 ≤ C.splitMultiplicity p := by omega
  have hforced := C.nonsplit_pencil_trace_subset_partner hvalid hcompat p hbge
    (C.forcedNonsplitLabels p) (fun b hb => hlabels b (hsubset hb))
    (C.forcedNonsplitLabels_through p)
  have hcoverSet : C.points ⊆ B.biUnion C.blockPoints := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨b, hb, hxb⟩
  by_cases hb2 : C.splitMultiplicity p = 2
  · have hcount : Fintype.card F - 1 ≤ (C.forcedNonsplitLabels p).card := by
      have := C.forcedNonsplitLabels_card_add p
      omega
    exact C.two_split_cover_impossible_after_forcing hvalid hcompat p hb2 B
      (C.forcedNonsplitLabels p) hlabels hcard hsubset hcount hforced hcoverSet
  · have hb3 : 3 ≤ C.splitMultiplicity p := by omega
    exact C.large_affine_pencil_cover_impossible hlocal p hb3
      (C.splitMultiplicity_le_order_add_one p) B (C.forcedNonsplitLabels p)
      hlabels hcard hsubset (C.forcedNonsplitLabels_card p) hforced hcoverSet

theorem no_small_block_cover
    (hvalid : C.Valid) (hcompat : C.Compatible)
    {rho : ℝ} {cap : ℕ} (hrho : 0 < rho)
    (hq : 4 ≤ Fintype.card F) (hocc : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (hconcentration : C.CoreConcentration rho) (hlocal : C.LocalCondition)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcard : B.card ≤ Fintype.card F) :
    ¬ ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b := by
  intro hcover
  obtain ⟨P, hbudget⟩ := C.core_cover_outside_pencil_budget
    hvalid hconcentration B hlabels hcard hcover
  rcases P with p | g
  · exact C.affine_pencil_cover_impossible_of_budget
      hvalid hcompat hocc hsize hlocal B hlabels hcard p hbudget hcover
  · have hforced := C.parallel_pencil_forced_label_count
      hvalid hcompat hrho hocc B hlabels hcover g hbudget
    apply C.parallel_cover_impossible_of_forced_count
      hvalid hcompat (by omega) g B hlabels hcard hforced
    intro x hx
    obtain ⟨b, hb, hxb⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨b, hb, hxb⟩

theorem block_cover_card_lower_bound
    (hvalid : C.Valid) (hcompat : C.Compatible)
    {rho : ℝ} {cap : ℕ} (hrho : 0 < rho)
    (hq : 4 ≤ Fintype.card F) (hocc : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (hconcentration : C.CoreConcentration rho) (hlocal : C.LocalCondition)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b) :
    Fintype.card F + 1 ≤ B.card := by
  by_contra hnot
  exact C.no_small_block_cover hvalid hcompat hrho hq hocc hsize
    hconcentration hlocal B hlabels (by omega) hcover

end
end Configuration
end Balanced

end OAI
