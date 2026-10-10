import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

theorem norm_four_sum_sub_le {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (a b c : α → β → γ → δ → ℂ)
    (h : ∀i j k p,a i j k p-b i j k p=c i j k p) :
    ‖(∑i,∑j,∑k,∑p,a i j k p)-(∑i,∑j,∑k,∑p,b i j k p)‖ ≤
      ∑i,∑j,∑k,∑p,‖c i j k p‖ := by
  simp_rw [←Finset.sum_sub_distrib,h]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => norm_sum_le _ _))))))

theorem four_sum_zero_cost_bounds {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (a b c : α → β → γ → δ → ℂ)
    (h : ∀i j k p,a i j k p-b i j k p=c i j k p)
    (L r₁ r₂ : ℝ)
    (hb : Real.exp (0*(L+1)^2)*(∑i,∑j,∑k,∑p,‖c i j k p‖)≤r₁ ∧
      Real.exp (0*(L+1)^2)*(∑i,∑j,∑k,∑p,‖c i j k p‖)≤r₂) :
    ‖(∑i,∑j,∑k,∑p,a i j k p)-(∑i,∑j,∑k,∑p,b i j k p)‖≤r₁ ∧
    ‖(∑i,∑j,∑k,∑p,a i j k p)-(∑i,∑j,∑k,∑p,b i j k p)‖≤r₂ := by
  simp only [zero_mul,Real.exp_zero,one_mul] at hb
  exact ⟨(norm_four_sum_sub_le a b c h).trans hb.1,
    (norm_four_sum_sub_le a b c h).trans hb.2⟩

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
