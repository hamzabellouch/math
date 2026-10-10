import OAI.Analysis.LipschitzHilbert.Trees.SourceWindowAverage
import OAI.Analysis.LipschitzHilbert.Estimates.TopWeight

namespace OAI

/-! The predictor uses displacement from a chosen good snapshot. Translate
its exact probability law and line-grid indices back to physical coordinates. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

/-- Translation of the normalized interval law, with its full remainder
already included in the original predictor construction. -/
theorem intervalProbability_map_add (a b t : ℝ) :
    (intervalProbability (a-t) (b-t)).map (fun x => x+t) = intervalProbability a b := by
  have hpre : (fun x : ℝ => x+t) ⁻¹' Icc a b = Icc (a-t) (b-t) := by
    ext x
    simp only [mem_preimage,mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  unfold intervalProbability
  rw [Measure.map_smul _ (by fun_prop),← hpre,
    ← Measure.restrict_map (by fun_prop) measurableSet_Icc,
    Measure.IsAddRightInvariant.map_add_right_eq_self]
  rw [show b-t-(a-t) = b-a by ring]

namespace FiniteLineGrid

def atSnapshot (g : FiniteLineGrid) (x₀ : ℝ) : FiniteLineGrid :=
  {g with origin := g.origin-x₀}

theorem atSnapshot_mem_root (g : FiniteLineGrid) (x₀ x : ℝ) :
    x-x₀ ∈ (g.atSnapshot x₀).root ↔ x ∈ g.root := by
  change (g.origin-x₀ ≤ x-x₀ ∧ x-x₀ < (g.origin-x₀)+g.width) ↔
    (g.origin ≤ x ∧ x < g.origin+g.width)
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem atSnapshot_rawIndex (g : FiniteLineGrid) (x₀ x : ℝ) (level : ℕ) :
    (g.atSnapshot x₀).rawIndex level (x-x₀) = g.rawIndex level x := by
  classical
  unfold rawIndex
  rw [g.atSnapshot_mem_root]
  simp only [atSnapshot,show x-x₀-(g.origin-x₀) = x-g.origin by ring]

theorem atSnapshot_index (g : FiniteLineGrid) (x₀ x : ℝ) (level : ℕ) :
    (g.atSnapshot x₀).index level (x-x₀) = g.index level x := by
  apply Fin.ext
  exact g.atSnapshot_rawIndex x₀ x (min level g.depth)

theorem snapshot_displacement_le_width (g : FiniteLineGrid) {x₀ x : ℝ}
    (h₀ : x₀ ∈ g.root) (hx : x ∈ g.root) : |x-x₀| ≤ g.width := by
  rw [abs_le]
  constructor <;> linarith [h₀.1,h₀.2,hx.1,hx.2]

/-- A predictor built in displacement coordinates has exactly the same
normalized average and fine-cell constancy in the physical window. -/
theorem snapshot_factor_transfer (g : FiniteLineGrid) (x₀ : ℝ) (level : ℕ)
    (P : ℝ → ℝ) (hP : Measurable P)
    (hint : Integrable P (intervalProbability (g.atSnapshot x₀).origin
      ((g.atSnapshot x₀).origin+(g.atSnapshot x₀).width)))
    (hpos : ∀ b, 0 ≤ P b)
    (havg : (∫ b, P b ∂intervalProbability (g.atSnapshot x₀).origin
      ((g.atSnapshot x₀).origin+(g.atSnapshot x₀).width)) ≤ 1)
    (hconst : ∀ b c, (g.atSnapshot x₀).index level b =
      (g.atSnapshot x₀).index level c → P b = P c) :
    Measurable (fun x => P (x-x₀)) ∧
    Integrable (fun x => P (x-x₀)) (intervalProbability g.origin (g.origin+g.width)) ∧
    (∀ x, 0 ≤ P (x-x₀)) ∧
    (∫ x, P (x-x₀) ∂intervalProbability g.origin (g.origin+g.width)) ≤ 1 ∧
    (∀ x z, g.index level x = g.index level z → P (x-x₀) = P (z-x₀)) := by
  have hmap : (intervalProbability (g.atSnapshot x₀).origin
      ((g.atSnapshot x₀).origin+(g.atSnapshot x₀).width)).map (fun b => b+x₀) =
      intervalProbability g.origin (g.origin+g.width) := by
    simpa only [atSnapshot,sub_add_eq_add_sub] using
      intervalProbability_map_add g.origin (g.origin+g.width) x₀
  have hemb : MeasurableEmbedding (fun b : ℝ => b+x₀) :=
    (Homeomorph.addRight x₀).isClosedEmbedding.measurableEmbedding
  refine ⟨hP.comp (by fun_prop),?_,fun x => hpos _,?_,?_⟩
  · rw [← hmap]
    exact hemb.integrable_map_iff.mpr (by simpa only [Function.comp_def,add_sub_cancel_right] using hint)
  · rw [← hmap,hemb.integral_map]
    simpa only [add_sub_cancel_right] using havg
  · intro x z hxz
    exact hconst _ _ (by rw [g.atSnapshot_index,g.atSnapshot_index,hxz])

end FiniteLineGrid

/-- Both parameterizations name the same physical point of the reference
line, so packet-motion estimates apply to the chosen snapshot. -/
theorem lineShift_snapshot (s y x₀ x : ℝ) :
    SlopeBox.lineShift s (x-x₀) (x₀,y+s*x₀) = (x,y+s*x) := by
  unfold SlopeBox.lineShift
  congr 1 <;> ring

end LipschitzHilbert

end

end OAI
