import OAI.Analysis.LipschitzHilbert.Phase.LocalSkippedPrediction

namespace OAI

/-! Assemble independently chosen source predictors on their original local
windows. The resulting factor is a function of the global fine-cell index. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.FiniteLineGrid

/-- Probability-normalized local factors patch to a nonnegative global
factor with ordinary cell averages, preserving the pointwise comparison. -/
theorem exists_patched_source_prediction (g : FiniteLineGrid) (coarse fine : ℕ)
    (hcf : coarse ≤ fine) (hf : fine ≤ g.depth)
    (good : Set ℝ) (beta error : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hF : ∀ i < g.branching^coarse, ∀ x, 0 ≤ F i x)
    (hint : ∀ i < g.branching^coarse,
      Integrable (F i) (intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
        ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)))
    (haverage : ∀ i < g.branching^coarse,
      (∫ x, F i x ∂intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
        ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)) ≤ 1)
    (hconstant : ∀ i < g.branching^coarse, ∀ x y,
      (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) x =
        (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) y → F i x = F i y)
    (hcompare : ∀ i < g.branching^coarse, ∀ x ∈ g.cell coarse i ∩ good,
      beta x ≤ Real.exp (error x)*F i x) :
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧ (∀ x, 0 ≤ Γ x) ∧
      (∀ x y, g.index fine x = g.index fine y → Γ x = Γ y) ∧
      (∀ i : Fin (g.branching^g.depth),
        (∫ x in {x | g.index coarse x = i}, Γ x ∂volume.restrict g.root) ≤
          (volume.restrict g.root).real {x | g.index coarse x = i}) ∧
      ∀ x ∈ g.root ∩ good, beta x ≤ Real.exp (error x)*Γ x := by
  have hsum (i : ℕ) (hi : i < g.branching^coarse) :
      (∫ x in g.cell coarse i, F i x) ≤ volume.real (g.cell coarse i) := by
    have h := ((g.lineWindow coarse i (fine-coarse)).window_average_le (F i)
      (hint i hi) (haverage i hi)).2
    simpa only [lineWindow_root] using h
  obtain ⟨Γ,hmeas,hpos,hconst,heq,havg⟩ := g.exists_patched_window_factor coarse fine hcf hf F
    (fun i hi x _ => hF i hi x) (by
      intro i hi x hx y hy hxy
      apply hconstant i hi x y
      have hg : coarse+(fine-coarse) ≤ g.depth := by omega
      apply g.lineWindow_index_of_global coarse i (fine-coarse) (fine-coarse) hi le_rfl hg hx hy
      simpa only [Nat.add_sub_of_le hcf] using hxy) hsum
  refine ⟨Γ,hmeas,hpos,hconst,havg,?_⟩
  intro x hx
  have hi : (g.index coarse x).val < g.branching^coarse := by
    change g.rawIndex (min coarse g.depth) x < g.branching^coarse
    rw [Nat.min_eq_left (hcf.trans hf)]
    exact rawIndex_lt (g := {g with depth := coarse}) le_rfl x
  rw [heq x hx.1]
  exact hcompare _ hi x ⟨(g.index_eq_iff_mem_cell (hcf.trans hf) hx.1 _).mp rfl,hx.2⟩

end LipschitzHilbert.FiniteLineGrid

end

end OAI
