import Mathlib
import OAI.Computability.VertexCover.Analysis.BatchFunctionOwnLipschitz

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

theorem integral_l1_le {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsProbabilityMeasure μ] (g : α → ι → ℝ)
    (hg : ∀ i, AEStronglyMeasurable (fun a => g a i) μ)
    (hb : ∀ a, ∑ i, |g a i| ≤ 1) :
    ∑ i, |∫ a, g a i ∂μ| ≤ 1 := by
  have hbi : ∀ a i, |g a i| ≤ 1 := by
    intro a i
    exact (Finset.single_le_sum (fun j _ => abs_nonneg (g a j)) (Finset.mem_univ i)).trans (hb a)
  have hi : ∀ i, Integrable (fun a => |g a i|) μ := by
    intro i
    exact (Integrable.of_bound (hg i) 1
      (Filter.Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hbi a i))).abs
  calc
    (∑ i, |∫ a, g a i ∂μ|) ≤ ∑ i, ∫ a, |g a i| ∂μ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun a => g a i)
    _ = ∫ a, ∑ i, |g a i| ∂μ := (integral_finsetSum _ (fun i _ => hi i)).symm
    _ ≤ ∫ _a, (1 : ℝ) ∂μ := integral_mono
      (integrable_finsetSum _ (fun i _ => hi i)) (integrable_const 1) hb
    _ = 1 := by simp

theorem finite_l1_le {α ι : Type*} [Fintype α] [Fintype ι]
    (g : α → ι → ℝ) (hb : ∀ a, ∑ i, |g a i| ≤ 1) :
    ∑ i, |(∑ a, g a i) / Fintype.card α| ≤ 1 := by
  classical
  by_cases he : IsEmpty α
  · let := he
    simp
  · have : Nonempty α := not_isEmpty_iff.mp he
    have hc : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
    simp only [abs_div, abs_of_nonneg hc.le, ← Finset.sum_div]
    apply (div_le_iff₀ hc).mpr
    calc
      (∑ i, |∑ a, g a i|) ≤ ∑ i, ∑ a, |g a i| := by
        exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ a, ∑ i, |g a i| := Finset.sum_comm
      _ ≤ ∑ _a : α, (1 : ℝ) := Finset.sum_le_sum (fun a _ => hb a)
      _ = 1 * Fintype.card α := by simp

end VertexCover.Average

namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

noncomputable def ownFiber (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (j : J) (i : Φ.Query d) : Finset (Φ.HiddenSeeds J) := by
  classical
  exact Finset.univ.filter (fun hidden => Φ.query (Φ.spliceSeeds J frozen hidden) j = i)

@[simp] theorem mem_ownFiber (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (j : J) (i : Φ.Query d) (hidden : Φ.HiddenSeeds J) :
    hidden ∈ Φ.ownFiber J frozen j i ↔ Φ.query (Φ.spliceSeeds J frozen hidden) j = i := by
  classical
  simp [ownFiber]

noncomputable def ownMean (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ) : ℝ := by
  classical
  exact VertexCover.finiteMean (fun hidden : Φ.ownFiber J frozen j i =>
    ∫ other, Φ.batchFunction (Φ.spliceSeeds J frozen hidden) J c0 A hA
      (Function.update other j s) ∂Φ.batchLaw J)

noncomputable def ownGradient (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ)
    (k : Fin (Φ.WeightDimension d)) : ℝ := by
  classical
  exact VertexCover.finiteMean (fun hidden : Φ.ownFiber J frozen j i =>
    ∫ other, Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
      (Function.update other j s) j k ∂Φ.batchLaw J)

theorem canonicalGradient_update_measurable (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (s : Fin (Φ.WeightDimension d) → ℝ) (k : Fin (Φ.WeightDimension d)) :
    Measurable (fun other : Φ.BatchWeights J =>
      Φ.canonicalGradient seed J c0 A hA (Function.update other j s) j k) := by
  classical
  exact (measurable_pi_apply k).comp ((measurable_pi_apply j).comp
    ((Φ.canonicalGradient_measurable seed J c0 A hA).comp
      (continuous_id.update j continuous_const).measurable))

theorem ownGradient_block_bound (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ) :
    ∑ k, |Φ.ownGradient J frozen c0 A hA j i s k| ≤ 1 := by
  classical
  apply VertexCover.Average.finite_l1_le
  intro hidden
  apply VertexCover.Average.integral_l1_le
  · intro k
    exact (Φ.canonicalGradient_update_measurable _ J c0 A hA j s k).aestronglyMeasurable
  · intro other
    exact Φ.canonicalGradient_block_bound _ J c0 A hA (Function.update other j s) j

theorem ownGradient_unused (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ)
    (k : Fin (Φ.WeightDimension d)) (hk : ∀ a : i.LocalLabel, i.slot a ≠ k) :
    Φ.ownGradient J frozen c0 A hA j i s k = 0 := by
  classical
  unfold ownGradient VertexCover.finiteMean
  have hz : ∀ hidden : Φ.ownFiber J frozen j i, ∀ other : Φ.BatchWeights J,
      Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
        (Function.update other j s) j k = 0 := by
    intro hidden other
    apply Φ.canonicalGradient_unused
    have hq := (Φ.mem_ownFiber J frozen j i hidden).mp hidden.property
    rw [hq]
    exact hk
  simp only [hz, integral_zero, Finset.sum_const_zero, zero_div]

theorem ownGradient_unsupported (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (hi : Φ.ownFiber J frozen j i = ∅)
    (s : Fin (Φ.WeightDimension d) → ℝ) : Φ.ownGradient J frozen c0 A hA j i s = 0 := by
  classical
  funext k
  unfold ownGradient VertexCover.finiteMean
  simp only [Fintype.card_coe, hi, Finset.card_empty, Nat.cast_zero, div_zero, Pi.zero_apply]

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
