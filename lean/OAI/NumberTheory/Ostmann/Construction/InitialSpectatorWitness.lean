import OAI.NumberTheory.Ostmann.Construction.InitialSpectatorSplit

namespace OAI

/-! # Fixing spectators preserves the positive initial amplitude -/
namespace Ostmann
open scoped Classical BigOperators

theorem exists_supported_complex_mean_witness {I : Type*} [Fintype I]
    (μ : I → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hmass : ∑ i, μ i = 1)
    (F : I → ℂ) (β : ℝ) (hmean : β ≤ ‖∑ i, (μ i : ℂ) * F i‖) :
    ∃ i, 0 < μ i ∧ β ≤ ‖F i‖ := by
  by_contra hn
  push Not at hn
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hμ j)).mp
    (show 0 < ∑ i, μ i by rw [hmass]; norm_num)
  have hbound (j : I) : μ j * ‖F j‖ ≤ μ j * β := by
    by_cases hj : 0 < μ j
    · exact mul_le_mul_of_nonneg_left (hn j hj).le (hμ j)
    · have hz : μ j = 0 := le_antisymm (le_of_not_gt hj) (hμ j)
      simp only [hz, zero_mul, le_refl]
  have hstrict : ∑ j, μ j * ‖F j‖ < ∑ j, μ j * β :=
    Finset.sum_lt_sum (fun j _ => hbound j)
      ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (hn i hi) hi⟩
  have hnrm : ‖∑ i, (μ i : ℂ) * F i‖ ≤ ∑ i, μ i * ‖F i‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ j)]
  rw [← Finset.sum_mul, hmass, one_mul] at hstrict
  exact (not_lt_of_ge (hmean.trans hnrm)) hstrict

end Ostmann

end OAI
