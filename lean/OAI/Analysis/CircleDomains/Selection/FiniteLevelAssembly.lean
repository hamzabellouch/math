import OAI.Analysis.CircleDomains.Topology.PathImageCount

namespace OAI

/-! Combining the physical-domain and flagged-point counts after the
free part of a level has been excluded.
-/

open Set Function Filter MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem pathImageCount_lt_top_iff (H : Set X) (γ : C(PathTime, X)) :
    pathImageCount H γ < ∞ ↔ (range γ ∩ H).Finite := by
  have he : pathImageCount H γ = ((range γ ∩ H).encard : ℝ≥0∞) := by
    rw [pathImageCount, ← ENNReal.tsum_set_one]
    rw [tsum_subtype (range γ ∩ H) (fun _ : X => (1 : ℝ≥0∞))]
    simp only [Set.indicator]
  rw [he]
  constructor
  · intro h
    by_contra hn
    have hi : (range γ ∩ H).Infinite := hn
    rw [hi.encard_eq] at h
    exact (not_lt_of_ge le_rfl) h
  · intro h
    exact_mod_cast h.encard_lt_top

theorem pathImageCount_le_of_cover (H A B : Set X) (γ : C(PathTime, X))
    (hcover : ∀ x ∈ range γ ∩ H, x ∈ A ∪ B) :
    pathImageCount H γ ≤ pathImageCount A γ + pathImageCount B γ := by
  rw [pathImageCount, pathImageCount, pathImageCount, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ range γ ∩ H
  · rcases hcover x hx with ha | hb
    · simp only [ite_eq_left hx, ite_eq_left (show x ∈ range γ ∩ A from ⟨hx.1, ha⟩)]
      exact le_self_add
    · simp only [ite_eq_left hx, ite_eq_left (show x ∈ range γ ∩ B from ⟨hx.1, hb⟩)]
      exact le_add_self
  · simp only [ite_eq_right hx]
    exact bot_le

theorem pathImageCount_mono_target {A B : Set X} (hAB : A ⊆ B) (γ : C(PathTime, X)) :
    pathImageCount A γ ≤ pathImageCount B γ := by
  unfold pathImageCount
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ range γ ∩ A
  · simp only [hx, show x ∈ range γ ∩ B from ⟨hx.1, hAB hx.2⟩, ite_true, le_refl]
  · simp only [hx, ite_false, zero_le]

theorem pathImageCount_level_le_of_no_free_hits
    (U Flags H : Set X) (γ : C(PathTime, X))
    (hfree : ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), x ∈ H) :
    pathImageCount H γ ≤ pathImageCount (U ∩ H) γ + pathImageCount (Flags ∩ H) γ := by
  apply pathImageCount_le_of_cover
  intro x hx
  by_cases hu : x ∈ U
  · exact Or.inl ⟨hu, hx.2⟩
  · by_cases hf : x ∈ Flags
    · exact Or.inr ⟨hf, hx.2⟩
    · exact (hfree ⟨x, ⟨hx.1, hu, hf⟩, hx.2⟩).elim

theorem finite_level_of_no_free_hits
    (U Flags H : Set X) (γ : C(PathTime, X))
    (hfree : ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), x ∈ H)
    (hU : pathImageCount (U ∩ H) γ < ∞)
    (hFlags : pathImageCount (Flags ∩ H) γ < ∞) :
    (range γ ∩ H).Finite :=
  (pathImageCount_lt_top_iff H γ).mp
    ((pathImageCount_level_le_of_no_free_hits U Flags H γ hfree).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hU, hFlags⟩))

end CircleDomainRigidity

end

end OAI
