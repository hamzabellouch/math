import OAI.Analysis.LipschitzHilbert.Trees.SourceWindowAverage
import OAI.Analysis.LipschitzHilbert.Fourier.SkippedLineAverage

namespace OAI

/-! Patch local source predictions by the actual global fine-cell profile.
Points outside the root share the first fiber's value, so global constancy
is preserved without any extra measurable-choice requirement. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.FiniteLineGrid

private theorem nonnegative_profile_on (P : ℝ → ℕ) (s : Set ℝ) (F : ℝ → ℝ)
    (hF : ∀ x ∈ s, 0 ≤ F x)
    (hconstant : ∀ x ∈ s, ∀ y ∈ s, P x = P y → F x = F y) :
    ∃ c : ℕ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ x ∈ s, F x = c (P x) := by
  classical
  let c := fun i => if h : ∃ x ∈ s, P x = i then F h.choose else 0
  refine ⟨c,?_,?_⟩
  · intro i
    dsimp only [c]
    split_ifs with h
    · exact hF _ h.choose_spec.1
    · exact le_rfl
  · intro x hx
    have h : ∃ y ∈ s, P y = P x := ⟨x,hx,rfl⟩
    dsimp only [c]
    rw [dite_eq_left h]
    exact hconstant x hx h.choose h.choose_spec.1 h.choose_spec.2.symm

/-- Local window factors assemble into one globally fine-cell-constant
nonnegative function, with the correct average on every coarse cell. -/
theorem exists_patched_window_factor (g : FiniteLineGrid) (coarse fine : ℕ)
    (hcf : coarse ≤ fine) (hf : fine ≤ g.depth)
    (F : ℕ → ℝ → ℝ)
    (hF : ∀ i < g.branching^coarse, ∀ x ∈ g.cell coarse i, 0 ≤ F i x)
    (hconstant : ∀ i < g.branching^coarse, ∀ x ∈ g.cell coarse i,
      ∀ y ∈ g.cell coarse i, g.index fine x = g.index fine y → F i x = F i y)
    (haverage : ∀ i < g.branching^coarse,
      (∫ x in g.cell coarse i, F i x) ≤ volume.real (g.cell coarse i)) :
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧ (∀ x, 0 ≤ Γ x) ∧
      (∀ x y, g.index fine x = g.index fine y → Γ x = Γ y) ∧
      (∀ x ∈ g.root, Γ x = F (g.index coarse x).val x) ∧
      (∀ i : Fin (g.branching^g.depth),
        (∫ x in {x | g.index coarse x = i}, Γ x ∂volume.restrict g.root) ≤
          (volume.restrict g.root).real {x | g.index coarse x = i}) := by
  classical
  let f := fun x => F (g.index coarse x).val x
  have hidx (x : ℝ) : (g.index coarse x).val < g.branching^coarse := by
    change g.rawIndex (min coarse g.depth) x < g.branching^coarse
    rw [Nat.min_eq_left (hcf.trans hf)]
    have h := rawIndex_lt (g := {g with depth := coarse}) (le_refl coarse) x
    exact h
  have hmem (x : ℝ) (hx : x ∈ g.root) : x ∈ g.cell coarse (g.index coarse x).val :=
    (g.index_eq_iff_mem_cell (hcf.trans hf) hx _).mp rfl
  obtain ⟨c,hc,heq⟩ := nonnegative_profile_on (fun x => (g.index fine x).val) g.root f
    (fun x hx => hF _ (hidx x) x (hmem x hx)) (by
      intro x hx y hy hxy
      have hxy' : g.index fine x = g.index fine y := Fin.ext hxy
      have hcoarse : g.index coarse x = g.index coarse y := by
        rw [g.index_ancestor hcf hf x,g.index_ancestor hcf hf y,hxy']
      dsimp only [f]
      rw [← hcoarse]
      exact hconstant _ (hidx x) x (hmem x hx) y (by simpa only [hcoarse] using hmem y hy) hxy')
  let Γ := fun x => c (g.index fine x).val
  refine ⟨Γ,?_,fun x => hc _,?_,?_,?_⟩
  · exact measurable_finite_profile (g.index fine) (g.measurable_index_fiber fine) (fun i => c i.val)
  · intro x y hxy
    dsimp only [Γ]
    rw [hxy]
  · intro x hx
    exact (heq x hx).symm
  · intro i
    have hset : {x | g.index coarse x = i} ∩ g.root =
        {x ∈ g.root | (g.index coarse x).val = i.val} := by
      ext x
      simp only [mem_inter_iff,mem_ofPred_eq,Fin.ext_iff]
      tauto
    rw [measureReal_restrict_apply (g.measurable_index_fiber coarse i),
      Measure.restrict_restrict (g.measurable_index_fiber coarse i),hset]
    by_cases hi : i.val < g.branching^coarse
    · rw [g.index_fiber_inter_root (hcf.trans hf) hi]
      have heq' : (∫ x in g.cell coarse i.val, Γ x) =
          ∫ x in g.cell coarse i.val, F i.val x := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro x hx
        have hroot := g.cell_subset_root coarse hi hx
        have hix := (g.index_eq_iff_mem_cell (hcf.trans hf) hroot i.val).mpr hx
        exact (heq x hroot).symm.trans (by dsimp only [f]; rw [hix])
      rw [heq']
      exact haverage i.val hi
    · have hempty : {x ∈ g.root | (g.index coarse x).val = i.val} = ∅ := by
        ext x
        simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false,not_and]
        intro _ hix
        exact hi (hix ▸ hidx x)
      rw [hempty]
      simp

end LipschitzHilbert.FiniteLineGrid

end

end OAI
