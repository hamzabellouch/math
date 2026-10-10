import OAI.NumberTheory.Ostmann.Construction.ScheduledHistoryEmbedding
import OAI.NumberTheory.Ostmann.Construction.FullWeightFrequencies
import OAI.NumberTheory.Ostmann.Construction.ConstituentAmplitudeEnergy

namespace OAI

/-! # The actual Fourier energy with the original bottom-frequency cutoff -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

noncomputable def clippedFullAtomFourierWeight {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (S : Finset ℤ) (V n : ℕ)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree S n) : ℂ :=
  if frequencyLeafWeight (singleFrequencyLeaf S V) n t = 1 then
    fullAtomTransferWeight role childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
      n x (frequencyTreeMap Subtype.val n t) else 0

theorem clippedFullAtomFourierWeight_square_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi Δ C K : ℝ) (hX : 0 < X)
    (hlo : Real.exp (Δ - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (S : Finset ℤ) (V n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree S n) :
    ‖clippedFullAtomFourierWeight role childBound pivotBound ranges ψ X lo hi S V n x t‖ ^ 2 ≤
      Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) *
        frequencyLeafWeight (singleFrequencyLeaf S V) n t := by
  unfold clippedFullAtomFourierWeight
  split_ifs with hcut
  · rw [hcut, mul_one]
    exact fullAtomFourierWeight_square_exp_le role childBound pivotBound ranges
      ψ X lo hi Δ C K hX hlo hψ n x _
  · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (Real.exp_pos _).le (frequencyLeafWeight_nonneg _
      (fun _ => by unfold singleFrequencyLeaf; split_ifs <;> norm_num) n t)

/-- Extending the internal frequency sets costs no multiplicity. All original
prime laws, bottom cutoffs and recursive support conditions remain in the sum. -/
theorem scheduled_full_fourier_energy_le {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X) (hlo : 1 < X * lo)
    (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (μ : A → ℝ) (hμ : ∀ q, 0 ≤ μ q) (values : A → CopyScheduleAtoms role n → ℕ) :
    (∑ a : ScheduledFrequencyIndex V n, ∑ q, μ q *
      ‖fullAtomTransferWeight role childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
        n (values q) (scheduledFrequencyHistory V n a)‖ ^ 2) ≤
      ∑ t : FrequencyTree ((transferFrequencyRange (V n)).erase 0) n, ∑ q, μ q *
        ‖clippedFullAtomFourierWeight role childBound pivotBound ranges ψ X lo hi
          ((transferFrequencyRange (V n)).erase 0) (V 0) n (values q) t‖ ^ 2 := by
  have h := scheduled_history_sum_le V hV n
    (fun t => ∑ q, μ q * ‖fullAtomTransferWeight role childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) n (values q) t‖ ^ 2)
    (fun _ => Finset.sum_nonneg (fun q _ => mul_nonneg (hμ q) (sq_nonneg _)))
    (fun a ha => ?_)
  · apply h.trans_eq
    apply Finset.sum_congr rfl
    intro t _
    unfold clippedFullAtomFourierWeight
    split_ifs with hcut
    · rfl
    · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]
  · apply Finset.sum_eq_zero
    intro q _
    have hz : fullAtomTransferWeight role childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) n (values q) (scheduledFrequencyHistory V n a) = 0 := by
      by_contra hw
      exact ha (fullAtomFourierWeight_all_frequencies_ne_zero role childBound pivotBound ranges
        ψ X lo hi hX hlo n (values q) _ hw)
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]

end Ostmann

end OAI
