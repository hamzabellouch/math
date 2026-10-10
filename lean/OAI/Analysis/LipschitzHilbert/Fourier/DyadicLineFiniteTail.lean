import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineCarleson
import OAI.Analysis.LipschitzHilbert.Estimates.CarlesonExponential

namespace OAI

/-! The exponential count bound for actual finite maximal dyadic families. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.DyadicLineGrid

attribute [local instance] Classical.propDecidable

theorem maximal_bad_finite_tail {ι B : Type*} [Fintype ι]
    (q top : ℤ) (f : B → ℝ → ℝ) (bin : ι → B) (level pos : ι → ℤ)
    (hunique : ∀ i j, bin i = bin j → level i = level j → pos i = pos j → i = j)
    {β C : ℝ} (hβ : 0 < β) (hC : 0 < C)
    (hmax : ∀ i, MaximalBad q top (Bad q (f (bin i)) β) (level i) (pos i))
    (hf : ∀ b, Measurable (f b)) (hbound : ∀ b x, 0 ≤ f b x ∧ f b x ≤ 1)
    (hsum : ∀ s : Finset B, ∀ x, (∑ b ∈ s, f b x) ≤ C)
    (rootLevel rootPos : ℤ)
    (hsub : ∀ i, cell q (level i) (pos i) ⊆ cell q rootLevel rootPos)
    (lambda : ℝ) :
    volume.real ({x | lambda < laminarCount (fun i => cell q (level i) (pos i)) x} ∩
      cell q rootLevel rootPos) ≤
      2 * scale rootLevel * Real.exp (-lambda / (2 * (C / β))) := by
  have hcarleson : ∀ P, P = cell q rootLevel rootPos ∨
      P ∈ range (fun i => cell q (level i) (pos i)) →
      (∑ i, if cell q (level i) (pos i) ⊆ P then volume.real (cell q (level i) (pos i)) else 0) ≤
        (C / β) * volume.real P := by
    intro P hP
    have hPm : MeasurableSet P := by
      rcases hP with rfl | ⟨i, rfl⟩
      · exact cell_measurable q rootLevel rootPos
      · exact cell_measurable q (level i) (pos i)
    have hPf : volume P ≠ ∞ := by
      rcases hP with rfl | ⟨i, rfl⟩ <;> exact measure_Ico_lt_top.ne
    exact maximal_bad_carleson_restricted q top f bin level pos hunique hβ hmax hf hbound hsum hPm hPf
  have hc := laminar_count_exponential_tail (fun i => cell q (level i) (pos i)) volume level
    (fun i => cell_measurable q (level i) (pos i)) measure_Ico_lt_top.ne hsub
    (fun i j hji hmeet => cell_subset_of_intersect hji (by simpa only [inter_comm] using hmeet))
    (div_pos hC hβ) hcarleson lambda
  have hlen : volume.real (Ico (left q rootLevel rootPos) (left q rootLevel (rootPos + 1))) =
      scale rootLevel := cell_length q rootLevel rootPos
  rw [hlen] at hc
  exact hc

end LipschitzHilbert.DyadicLineGrid

end

end OAI
