import Mathlib.Order.Interval.Finset.Fin
import OAI.Combinatorics.BalancedRyser.Probability.ExposureSchedule

namespace OAI

namespace Balanced.ExposureInterleaving

theorem previous_card_eq_time {n m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (t : Fin (n + m)) :
    (previousD γ (timeEquiv hγ t)).card +
      (previousC γ (timeEquiv hγ t)).card = t.val := by
  classical
  rw [← Finset.card_disjSum]
  have heq : (previousD γ (timeEquiv hγ t)).disjSum
      (previousC γ (timeEquiv hγ t)) =
      (Finset.Iio t).map (timeEquiv hγ).toEmbedding := by
    ext s
    rcases s with i | j
    · simp only [Finset.inl_mem_disjSum, mem_previousD_iff_time hγ, Finset.mem_map,
        Finset.mem_Iio, Equiv.toEmbedding_apply]
      constructor
      · intro hi
        exact ⟨deletionTime hγ i, hi, by simp [deletionTime]⟩
      · rintro ⟨u, hu, he⟩
        have h : u = deletionTime hγ i := by
          apply (timeEquiv hγ).injective
          simpa [deletionTime] using he
        simpa [h] using hu
    · simp only [Finset.inr_mem_disjSum, mem_previousC_iff_time hγ, Finset.mem_map,
        Finset.mem_Iio, Equiv.toEmbedding_apply]
      constructor
      · intro hj
        exact ⟨coverTime hγ j, hj, by simp [coverTime]⟩
      · rintro ⟨u, hu, he⟩
        have h : u = coverTime hγ j := by
          apply (timeEquiv hγ).injective
          simpa [coverTime] using he
        simpa [h] using hu
  rw [heq, Finset.card_map, Fin.card_Iio]

theorem remaining_card_eq_time {n m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (t : Fin (n + m)) :
    (remainingD γ (timeEquiv hγ t)).card +
      (remainingC γ (timeEquiv hγ t)).card = n + m - t.val := by
  have hD := previousD_add_remainingD γ (timeEquiv hγ t)
  have hC := previousC_add_remainingC γ (timeEquiv hγ t)
  have hT := previous_card_eq_time hγ t
  omega
end Balanced.ExposureInterleaving

end OAI
