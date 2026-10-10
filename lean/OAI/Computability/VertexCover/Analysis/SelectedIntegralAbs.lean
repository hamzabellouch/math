import Mathlib
import OAI.Computability.VertexCover.Reduction.PairEventMean

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

noncomputable def fiberAverage {α β : Type*} [Fintype α]
    (q : α → β) (f : β → α → ℝ) (i : β) : ℝ := by
  classical
  exact (∑ a ∈ Finset.univ.filter (fun a => q a = i), f i a) /
    (Finset.univ.filter (fun a => q a = i)).card

theorem sum_fiberAverage {α β : Type*} [Fintype α] [Fintype β]
    (q : α → β) (f : β → α → ℝ) :
    (∑ a, fiberAverage q f (q a)) = ∑ a, f (q a) a := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ q (fun a => fiberAverage q f (q a)),
    ← Finset.sum_fiberwise Finset.univ q (fun a => f (q a) a)]
  apply Finset.sum_congr rfl
  intro i hi
  have hq : ∀ a ∈ Finset.univ.filter (fun a => q a = i), q a = i := by
    intro a ha; exact (Finset.mem_filter.mp ha).2
  calc
    _ = ∑ _a ∈ Finset.univ.filter (fun a => q a = i), fiberAverage q f i := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hq a ha]
    _ = (Finset.univ.filter (fun a => q a = i)).card * fiberAverage q f i := by simp
    _ = ∑ a ∈ Finset.univ.filter (fun a => q a = i), f i a := by
      unfold fiberAverage
      by_cases hz : (Finset.univ.filter (fun a => q a = i)).card = 0
      · have he := Finset.card_eq_zero.mp hz
        simp [he]
      · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hq a ha]

theorem finiteMean_fiber_tower {α β : Type*} [Fintype α] [Fintype β]
    (q : α → β) (f : β → α → ℝ) :
    (by classical exact VertexCover.finiteMean (fun a : α =>
      VertexCover.finiteMean (fun a' : Finset.univ.filter (fun a' => q a' = q a) =>
        f (q a) a'))) = VertexCover.finiteMean (fun a : α => f (q a) a) := by
  classical
  have he : ∀ i, VertexCover.finiteMean (fun a : Finset.univ.filter (fun a => q a = i) => f i a) =
      fiberAverage q f i := by
    intro i
    unfold VertexCover.finiteMean fiberAverage
    rw [Finset.sum_coe_sort, Fintype.card_coe]
  simp_rw [he]
  unfold VertexCover.finiteMean
  rw [sum_fiberAverage]

theorem finiteMean_fiber_tower_of_mem {α β : Type*} [Fintype α] [Fintype β]
    (q : α → β) (f : β → α → ℝ) (T : β → Finset α)
    (hT : ∀ i a, a ∈ T i ↔ q a = i) :
    VertexCover.finiteMean (fun a : α =>
      VertexCover.finiteMean (fun a' : T (q a) => f (q a) a')) =
      VertexCover.finiteMean (fun a : α => f (q a) a) := by
  classical
  have he : T = fun i => Finset.univ.filter (fun a => q a = i) := by
    funext i
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hT]
  subst T
  exact finiteMean_fiber_tower q f

theorem selected_integral_abs_le {α Ω K : Type*} [Fintype α] [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Finset K) (F : α → Ω → K → ℝ)
    (hF : ∀ a k, Integrable (fun x => F a x k) μ) :
    (∑ k ∈ T, |(∑ a, ∫ x, F a x k ∂μ) / Fintype.card α|) ≤
      (∑ a, ∫ x, ∑ k ∈ T, |F a x k| ∂μ) / Fintype.card α := by
  classical
  have hc : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  simp_rw [abs_div, abs_of_nonneg hc]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ hc
  calc
    _ ≤ ∑ k ∈ T, ∑ a, ∫ x, |F a x k| ∂μ := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ ∑ a, |∫ x, F a x k ∂μ| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := Finset.sum_le_sum (fun a _ => by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (F a · k))
    _ = ∑ a, ∑ k ∈ T, ∫ x, |F a x k| ∂μ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (integral_finsetSum T (fun k _ => (hF a k).abs)).symm

end VertexCover.Average


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
