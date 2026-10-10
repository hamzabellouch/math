import OAI.MeasureTheory.Falconer.Estimates.IncidentCoarseRounding

namespace OAI

/-! The common-grid cover of retained fine lines is bounded by the
retained incident coarse pencils, in the reverse direction needed when
applying the regular-set alternative after refinement. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem rounded_candidates_reverse {δ : ℝ} (hδ : 0 < δ)
    (l a : Space 2) (L : ℕ) (ha : a ∈ roundedStripCandidates δ (l 0) (l 1) L) :
    coarsePlanarRound δ l ∈ roundedStripCandidates δ (a 0) (a 1) L := by
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
  have hjb := Finset.mem_Icc.mp hj
  apply Finset.mem_image.mpr
  refine ⟨round (l 1/δ),?_,?_⟩
  · simp only [gridLine_snd,mul_div_cancel_left₀ _ hδ.ne',round_intCast]
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · simp only [gridLine_fst,mul_div_cancel_left₀ _ hδ.ne',round_intCast]
    rfl

theorem retained_coarse_cover_card {δ : ℝ} (hδ : 0 < δ)
    (C : Finset (Space 2)) (T D : Space 2 → Finset (Space 2))
    (hc : ∀ c ∈ C, |c 0| ≤ 1)
    (hres : ∀ c ∈ C, ∀ l ∈ T c, |c 1-l 0*c 0-l 1| ≤ 4*δ)
    (hretain : ∀ c ∈ C, ∀ l ∈ T c, roundedIncidentLine δ c (l 0) ∈ D c) :
    (((C.biUnion T).image (coarsePlanarRound δ)).card:ℝ) ≤
      13*((C.biUnion D).card:ℝ) := by
  have hsub : (C.biUnion T).image (coarsePlanarRound δ) ⊆
      (C.biUnion D).biUnion (fun a => roundedStripCandidates δ (a 0) (a 1) 6) := by
    intro b hb
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c,hcC,hl⟩ := Finset.mem_biUnion.mp hl
    refine Finset.mem_biUnion.mpr ⟨roundedIncidentLine δ c (l 0),
      Finset.mem_biUnion.mpr ⟨c,hcC,hretain c hcC l hl⟩,?_⟩
    exact rounded_candidates_reverse hδ l _ 6
      (roundedIncidentLine_mem_candidates hδ c (hc c hcC) (hres c hcC l hl) 6 (by norm_num))
  calc
    _ ≤ ∑ a ∈ C.biUnion D, ((roundedStripCandidates δ (a 0) (a 1) 6).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ C.biUnion D, (13:ℝ) := Finset.sum_le_sum fun a _ => by
      exact_mod_cast roundedStripCandidates_card_le δ (a 0) (a 1) 6
    _ = _ := by simp; ring

end Falconer

end OAI
