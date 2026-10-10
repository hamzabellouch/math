import Mathlib
import OAI.Computability.VertexCover.Analysis.OwnGradientUnsupported

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Average
open MeasureTheory

theorem finite_abs_le {α : Type*} [Fintype α] (g : α → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hg : ∀ a, |g a| ≤ B) :
    |(∑ a, g a) / Fintype.card α| ≤ B := by
  classical
  by_cases he : IsEmpty α
  · let := he
    simpa using hB
  · have : Nonempty α := not_isEmpty_iff.mp he
    have hc : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
    rw [abs_div, abs_of_nonneg hc.le]
    apply (div_le_iff₀ hc).mpr
    calc
      |∑ a, g a| ≤ ∑ a, |g a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : α, B := Finset.sum_le_sum (fun a _ => hg a)
      _ = B * Fintype.card α := by simp [mul_comm]

theorem integral_lipschitz {α E : Type*} [MeasurableSpace α] [PseudoMetricSpace E]
    (μ : Measure α) [IsProbabilityMeasure μ] {C : NNReal} (F : E → α → ℝ)
    (hi : ∀ x, Integrable (F x) μ) (hF : ∀ a, LipschitzWith C (fun x => F x a)) :
    LipschitzWith C (fun x => ∫ a, F x a ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← integral_sub (hi x) (hi y)]
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun a => F x a - F y a) (C := (C : ℝ) * dist x y)
    (Filter.Eventually.of_forall (fun a => by
      simpa only [dist_eq_norm] using (hF a).dist_le_mul x y))
  simpa only [Real.dist_eq, Real.norm_eq_abs, probReal_univ, mul_one] using h

end VertexCover.Average

namespace VertexCover.LabelCover
open MeasureTheory

theorem ownMean_lipschitz (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) :
    LipschitzWith 1 (Φ.ownMean J frozen c0 A hA j i) := by
  classical
  have hI : ∀ hidden : Φ.ownFiber J frozen j i,
      LipschitzWith 1 (fun s => ∫ other,
        Φ.batchFunction (Φ.spliceSeeds J frozen hidden) J c0 A hA
          (Function.update other j s) ∂Φ.batchLaw J) := by
    intro hidden
    apply VertexCover.Average.integral_lipschitz
    · intro s
      exact VertexCover.Cube.integrable_continuous_block
        ((Φ.batchFunction_continuous _ J c0 A hA).comp
          (continuous_id.update j continuous_const))
    · intro other
      exact Φ.batchFunction_own_lipschitz _ J c0 A hA other j
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, ownMean, VertexCover.finiteMean,
    ← sub_div, ← Finset.sum_sub_distrib]
  apply VertexCover.Average.finite_abs_le (hB := dist_nonneg)
  intro hidden
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using (hI hidden).dist_le_mul s t

theorem ownGradient_measurable (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (k : Fin (Φ.WeightDimension d)) :
    Measurable (fun s => Φ.ownGradient J frozen c0 A hA j i s k) := by
  classical
  have hI : ∀ hidden : Φ.ownFiber J frozen j i,
      StronglyMeasurable (fun s => ∫ other,
        Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
          (Function.update other j s) j k ∂Φ.batchLaw J) := by
    intro hidden
    apply StronglyMeasurable.integral_prod_right
    apply Measurable.stronglyMeasurable
    exact (measurable_pi_apply k).comp ((measurable_pi_apply j).comp
      ((Φ.canonicalGradient_measurable _ J c0 A hA).comp
        (continuous_snd.update j continuous_fst).measurable))
  unfold ownGradient VertexCover.finiteMean
  exact (Finset.measurable_sum _ (fun hidden _ => (hI hidden).measurable)).div_const _

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
