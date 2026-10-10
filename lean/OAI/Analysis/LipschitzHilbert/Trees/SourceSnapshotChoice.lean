import OAI.Analysis.LipschitzHilbert.Phase.SourceMarkedPrediction

namespace OAI

/-! Snapshots are chosen only on one fixed line. A cell missing the good
set has the constant factor one. No measurable choice across lines is used. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.FiniteLineGrid
attribute [local instance] Classical.propDecidable

/-- Patch local predictors selected at good snapshots. Factor-two drop
comparison converts their snapshot errors into actual pointwise errors. -/
theorem exists_marked_prediction_from_snapshots (g : FiniteLineGrid)
    (coarse fine : ℕ) (hcf : coarse ≤ fine) (hf : fine ≤ g.depth)
    (marked : ℕ → Prop) (good : Set ℝ) (beta u : ℝ → ℝ)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hpredict : ∀ i < g.branching^coarse, marked i →
      ∀ x₀ ∈ g.cell coarse i ∩ good,
      ∃ F : ℝ → ℝ,
        (∀ x, 0 ≤ F x) ∧
        Integrable F (intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
          ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)) ∧
        (∫ x, F x ∂intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
          ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)) ≤ 1 ∧
        (∀ x z, (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) x =
          (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) z → F x = F z) ∧
        ∀ x ∈ g.cell coarse i ∩ good, beta x ≤ Real.exp (ρ*u x₀)*F x)
    (hdrop : ∀ i < g.branching^coarse, marked i →
      ∀ x₀ ∈ g.cell coarse i ∩ good, ∀ x ∈ g.cell coarse i ∩ good,
        u x₀/2 ≤ u x) :
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧ (∀ x, 0 ≤ Γ x) ∧
      (∀ x z, g.index fine x = g.index fine z → Γ x = Γ z) ∧
      (∀ i : Fin (g.branching^g.depth),
        (∫ x in {x | g.index coarse x = i}, Γ x ∂volume.restrict g.root) ≤
          (volume.restrict g.root).real {x | g.index coarse x = i}) ∧
      (∀ x ∈ g.root, ¬marked (g.index coarse x).val → Γ x = 1) ∧
      ∀ x ∈ g.root ∩ good, g.markedValue coarse marked beta x ≤
        Real.exp (g.markedError coarse marked (fun x => (2*ρ)*u x) x)*Γ x := by
  have hlocal (i : ℕ) (hi : i < g.branching^coarse) (hm : marked i) :
      ∃ F : ℝ → ℝ,
        (∀ x, 0 ≤ F x) ∧
        Integrable F (intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
          ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)) ∧
        (∫ x, F x ∂intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
          ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)) ≤ 1 ∧
        (∀ x z, (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) x =
          (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) z → F x = F z) ∧
        ∀ x ∈ g.cell coarse i ∩ good, beta x ≤ Real.exp ((2*ρ)*u x)*F x := by
    by_cases hne : (g.cell coarse i ∩ good).Nonempty
    · obtain ⟨x₀,hx₀⟩ := hne
      obtain ⟨F,hpos,hint,havg,hconst,hcomp⟩ := hpredict i hi hm x₀ hx₀
      refine ⟨F,hpos,hint,havg,hconst,?_⟩
      intro x hx
      have herr := source_error_of_drop_comparability hρ (hdrop i hi hm x₀ hx₀ x hx)
        (le_refl (ρ*u x₀))
      exact (hcomp x hx).trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr herr) (hpos x))
    · let := intervalProbability_isProbability
        (show (g.lineWindow coarse i (fine-coarse)).origin <
          (g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width by
          linarith [(g.lineWindow coarse i (fine-coarse)).width_pos])
      refine ⟨fun _ => 1,fun _ => zero_le_one,integrable_const 1,?_,fun _ _ _ => rfl,?_⟩
      · simp
      · intro x hx
        exact (hne ⟨x,hx⟩).elim
  choose F hF using hlocal
  exact g.exists_marked_source_prediction coarse fine hcf hf marked good beta
    (fun x => (2*ρ)*u x) (fun i => if hi : i < g.branching^coarse then
      if hm : marked i then F i hi hm else fun _ => 1 else fun _ => 1)
    (fun i hi hm x => by simpa only [dite_eq_left hi,dite_eq_left hm] using (hF i hi hm).1 x)
    (fun i hi hm => by simpa only [dite_eq_left hi,dite_eq_left hm] using (hF i hi hm).2.1)
    (fun i hi hm => by simpa only [dite_eq_left hi,dite_eq_left hm] using (hF i hi hm).2.2.1)
    (fun i hi hm x z hxz => by
      simpa only [dite_eq_left hi,dite_eq_left hm] using (hF i hi hm).2.2.2.1 x z hxz)
    (fun i hi hm x hx => by
      simpa only [dite_eq_left hi,dite_eq_left hm] using (hF i hi hm).2.2.2.2 x hx)

end LipschitzHilbert.FiniteLineGrid

end

end OAI
