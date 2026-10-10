import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open Set
open scoped NNReal

theorem exists_lipschitz_lift_of_antilipschitz {X U V : Type*}
    [MetricSpace X] [MetricSpace U] [MetricSpace V]
    (F : U → V) (K : ℝ≥0) (hF : AntilipschitzWith K F)
    (g : X → V) (L : ℝ≥0) (hg : LipschitzWith L g)
    (hinto : Set.range g ⊆ Set.range F) :
    ∃ h : X → U, LipschitzWith (K * L) h ∧ ∀ x, F (h x) = g x := by
  classical
  have hpre : ∀ x : X, ∃ u : U, F u = g x := fun x => hinto ⟨x, rfl⟩
  choose h hh using hpre
  refine ⟨h, ?_, hh⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hb := hF.le_mul_dist (h x) (h y)
  rw [hh x, hh y] at hb
  calc
    dist (h x) (h y) ≤ (K : ℝ) * dist (g x) (g y) := hb
    _ ≤ (K : ℝ) * ((L : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hg.dist_le_mul x y) K.coe_nonneg
    _ = ((K * L : ℝ≥0) : ℝ) * dist x y := by rw [NNReal.coe_mul]; ring

end

end RieszRectifiability

end OAI
