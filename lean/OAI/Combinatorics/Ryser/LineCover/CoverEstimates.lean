import OAI.Combinatorics.Ryser.LineCover.CleanCover

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n : ℕ}

theorem filter_incidence_eq_inter (X : Finset (Point F)) (l : AffineLine F) :
    (X.filter fun x => Incidence x l) = X ∩ linePoints l := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter, mem_linePoints]

theorem sdiff_coveredPoints_eq (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    X \ coveredPoints Incidence X L = X \ L.biUnion linePoints := by
  rw [coveredPoints_eq_inter_biUnion]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · rintro ⟨hx, hn⟩
    exact ⟨hx, fun h => hn ⟨hx, h⟩⟩
  · rintro ⟨hx, hn⟩
    exact ⟨hx, fun h => hn h.2⟩

theorem survivors_ignore_clean_line_eq (ω : Fin n → Outcome shapes D)
    (L : Finset (AffineLine F)) {l : AffineLine F} (hl : l ∈ cleanLines ω L) :
    survivors {linePoints l} ω = survivors ∅ ω := by
  simpa only [Finset.insert_empty] using
    (survivors_insert_eq_of_not_selected (ignore := ∅)
      (cleanLines_not_selected hl))

theorem clean_cover_count_bounds (ω : Fin n → Outcome shapes D)
    (L : Finset (AffineLine F)) (τ δ e0 e1 b : ℝ)
    (hδ : 0 < δ) (hτ : δ ≤ τ) (he1 : 0 ≤ e1)
    (htotal : τ * (Fintype.card F : ℝ) ^ 2 - e0 ≤ (survivors ∅ ω).card)
    (hlines : ∀ l : AffineLine F,
      ((survivors {linePoints l} ω ∩ linePoints l).card : ℝ) ≤
        τ * (Fintype.card F : ℝ) + e1)
    (hmiss : ((survivors ∅ ω \ L.biUnion linePoints).card : ℝ) ≤ b)
    (hcard : L.card ≤ Fintype.card F) :
    (overlapExcess Incidence (survivors ∅ ω) (cleanLines ω L) : ℝ) ≤
        e0 + (Fintype.card F : ℝ) * e1 + b ∧
      (Fintype.card F : ℝ) - (cleanLines ω L).card ≤
        (e0 + (Fintype.card F : ℝ) * e1 + b) / (δ * Fintype.card F) := by
  have hq : 0 < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := F)
  apply cover_count_bounds Incidence (survivors ∅ ω) (cleanLines ω L)
    τ (Fintype.card F) e0 e1 b δ hδ hτ hq he1 htotal
  · intro l hl
    have hfilter :
        @Finset.filter _ (fun x => Incidence x l)
          (fun x => Classical.propDecidable (Incidence x l)) (survivors ∅ ω) =
          (survivors ∅ ω).filter (fun x => Incidence x l) :=
      Finset.filter_congr_decidable _ _ _
    rw [hfilter, filter_incidence_eq_inter, ← survivors_ignore_clean_line_eq ω L hl]
    exact hlines l
  · rw [sdiff_coveredPoints_eq, ← survivors_sdiff_cleanLines]
    exact hmiss
  · exact_mod_cast (Finset.card_le_card (cleanLines_subset ω L)).trans hcard

end RyserCoveringCounterexample.LineCover

end

end OAI
