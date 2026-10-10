import OAI.MeasureTheory.Falconer.Estimates.FinePacketCounts

namespace OAI

/-! Cell-dependent packets retain original fine tubes, and both their total
size and their common coarse cover are bounded by the original configuration. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem original_coarse_packets {δ ρ : ℝ} (hδ : 0 ≤ δ) (hρ : 0 < ρ) (hδρ : δ ≤ ρ)
    (P C : Finset (Space 2)) (V T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2)
    (hnear : ∀ p ∈ P, dist p (q p) ≤ ρ)
    (hCchart : ∀ c ∈ C, |c 0| ≤ 1)
    (hV : ∀ p ∈ P, ∀ l ∈ V p, |l 0| ≤ 1 ∧ TubeIncident δ p l)
    (hT : ∀ c ∈ C, T c ⊆ ((P.filter fun p => q p = c).biUnion V).image
      (fun l => roundedIncidentLine ρ c (l 0))) :
    let U := fun c => (P.filter fun p => q p = c).biUnion V
    let G := fineCoarsePacket ρ C U
    (∀ a ∈ C.biUnion T, (G a).Nonempty) ∧
    (∀ a, G a ⊆ P.biUnion V) ∧
    (∀ c ∈ C, ∀ p ∈ P, q p = c → ∀ l ∈ V p,
      l ∈ G (roundedIncidentLine ρ c (l 0))) ∧
    (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ 13*((P.biUnion V).card:ℝ) ∧
    ((C.biUnion T).card:ℝ) ≤ 13*(((P.biUnion V).image (coarsePlanarRound ρ)).card:ℝ) := by
  let U := fun c => (P.filter fun p => q p = c).biUnion V
  let W := C.biUnion fun c => (U c).image (fun l => roundedIncidentLine ρ c (l 0))
  have hUU : C.biUnion U ⊆ P.biUnion V := by
    intro l hl
    obtain ⟨c,_,hlc⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨p,hp,hlp⟩ := Finset.mem_biUnion.mp hlc
    exact Finset.mem_biUnion.mpr ⟨p,(Finset.mem_filter.mp hp).1,hlp⟩
  have hTW : C.biUnion T ⊆ W := by
    intro a ha
    obtain ⟨c,hc,ha⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨c,hc,hT c hc ha⟩
  have hres : ∀ c ∈ C, ∀ l ∈ U c, |c 1-l 0*c 0-l 1| ≤ 4*ρ := by
    intro c _ l hl
    obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨hp,hpc⟩ := Finset.mem_filter.mp hp
    have hc : dist p c ≤ ρ := by simpa only [hpc] using hnear p hp
    exact moved_point_residual hδ hρ hδρ p c l hc (hV p hp l hl).1 (hV p hp l hl).2
  refine ⟨fun a ha => fineCoarsePacket_nonempty C U (hTW ha),?_,?_,?_,?_⟩
  · intro a
    exact (Finset.filter_subset _ _).trans hUU
  · intro c hc p hp hpc l hl
    have hlU : l ∈ U c := Finset.mem_biUnion.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,hpc⟩,hl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨c,hc,hlU⟩,c,hc,hlU,rfl⟩
  · calc
      _ ≤ ∑ a ∈ W, ((fineCoarsePacket ρ C U a).card:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hTW (fun a _ _ => Nat.cast_nonneg _)
      _ ≤ 13*((C.biUnion U).card:ℝ) := by
        exact_mod_cast sum_fineCoarsePacket_card hρ C U hCchart hres
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hUU)) (by norm_num)
  · calc
      _ ≤ (W.card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hTW)
      _ ≤ 13*(((C.biUnion U).image (coarsePlanarRound ρ)).card:ℝ) :=
        incident_coarse_union_card hρ C U hCchart hres
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hUU))) (by norm_num)

end Falconer

end OAI
