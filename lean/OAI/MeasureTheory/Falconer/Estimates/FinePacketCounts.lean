import OAI.MeasureTheory.Falconer.Estimates.IncidentCoarseRounding
import OAI.MeasureTheory.Falconer.Incidence.FrozenPacketSelection

namespace OAI

/-! Original fine tubes have bounded multiplicity among cell-dependent
coarse packets. Thus freezing packet sizes preserves the needed total bound. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def fineCoarsePacket (Δ : ℝ) (C : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (a : Space 2) : Finset (Space 2) :=
  (C.biUnion T).filter fun l =>
    ∃ c ∈ C, l ∈ T c ∧ roundedIncidentLine Δ c (l 0) = a

theorem fineCoarsePacket_nonempty {Δ : ℝ} (C : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) {a : Space 2}
    (ha : a ∈ C.biUnion fun c => (T c).image (fun l => roundedIncidentLine Δ c (l 0))) :
    (fineCoarsePacket Δ C T a).Nonempty := by
  obtain ⟨c,hc,ha⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨l,hl,he⟩ := Finset.mem_image.mp ha
  exact ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨c,hc,hl⟩,c,hc,hl,he⟩⟩

theorem fineCoarsePacket_card_le (Δ : ℝ) (C : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (a : Space 2) :
    (fineCoarsePacket Δ C T a).card ≤ (C.biUnion T).card :=
  Finset.card_filter_le _ _

theorem sum_fineCoarsePacket_card {Δ : ℝ} (hΔ : 0 < Δ)
    (C : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hc : ∀ c ∈ C, |c 0| ≤ 1)
    (hres : ∀ c ∈ C, ∀ l ∈ T c, |c 1-l 0*c 0-l 1| ≤ 4*Δ) :
    (∑ a ∈ C.biUnion (fun c => (T c).image (fun l => roundedIncidentLine Δ c (l 0))),
      (fineCoarsePacket Δ C T a).card) ≤ 13*(C.biUnion T).card := by
  let V := C.biUnion fun c => (T c).image (fun l => roundedIncidentLine Δ c (l 0))
  have hswap : (∑ a ∈ V, (fineCoarsePacket Δ C T a).card) =
      ∑ l ∈ C.biUnion T, (V.filter fun a =>
        ∃ c ∈ C, l ∈ T c ∧ roundedIncidentLine Δ c (l 0) = a).card := by
    simp only [fineCoarsePacket,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  calc
    _ ≤ ∑ _l ∈ C.biUnion T, 13 := by
      apply Finset.sum_le_sum
      intro l _
      have hsub : (V.filter fun a => ∃ c ∈ C, l ∈ T c ∧
          roundedIncidentLine Δ c (l 0) = a) ⊆ roundedStripCandidates Δ (l 0) (l 1) 6 := by
        intro a ha
        obtain ⟨_,c,hcC,hl,he⟩ := Finset.mem_filter.mp ha
        rw [← he]
        exact roundedIncidentLine_mem_candidates hΔ c (hc c hcC) (hres c hcC l hl) 6 (by norm_num)
      exact (Finset.card_le_card hsub).trans (roundedStripCandidates_card_le Δ (l 0) (l 1) 6)
    _ = _ := by simp; omega

end Falconer

end OAI
