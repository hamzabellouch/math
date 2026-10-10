import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstSignedTransform
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSchwartzTail

namespace OAI

/-! # The discarded odd kernels are a genuine Schwartz frequency tail -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_kernel_le_frequency (z : QuadraticFrequencyIndex) :
    (z.2.1.val : ℕ) ≤ (quadraticFrequencyValue z).natAbs := by
  have ha : (z.1 : ℤ) ≠ 0 := by
    have h := z.1.property
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h <;> rw [h] <;> norm_num
  unfold quadraticFrequencyValue
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  calc
    _ ≤ (z.2.2 : ℕ) ^ 2 * (z.2.1.val : ℕ) :=
      Nat.le_mul_of_pos_left _ (pow_pos z.2.2.property 2)
    _ ≤ (z.1 : ℤ).natAbs * ((z.2.2 : ℕ) ^ 2 * (z.2.1.val : ℕ)) :=
      Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr ha)
    _ = _ := by ring

theorem quadratic_signed_kernel_tail_bound (F : ℤ → ℂ)
    (hF : Summable (fun h => ‖F h‖)) (K : ℕ) :
    ‖∑' z : QuadraticFrequencyIndex,
      if K < (z.2.1.val : ℕ) then F (quadraticFrequencyValue z) else 0‖ ≤
      ∑' h : ℤ, if K < h.natAbs then ‖F h‖ else 0 := by
  let G : ℤ → ℝ := fun h => if K < h.natAbs then ‖F h‖ else 0
  have hG : Summable G := by
    apply Summable.of_nonneg_of_le (fun _ => by dsimp [G]; split_ifs <;> positivity) _ hF
    intro h
    dsimp [G]
    split_ifs <;> simp
  have hGi := hG.comp_injective quadraticFrequencyValue_injective
  have hp (z : QuadraticFrequencyIndex) :
      ‖if K < (z.2.1.val : ℕ) then F (quadraticFrequencyValue z) else 0‖ ≤
        G (quadraticFrequencyValue z) := by
    by_cases hz : K < (z.2.1.val : ℕ)
    · have hi := hz.trans_le (quadratic_kernel_le_frequency z)
      simp only [hz, G, hi, ite_true]
      exact le_rfl
    · simp only [hz, ite_false, norm_zero]
      dsimp [G]
      split_ifs <;> positivity
  have hpi : Summable (fun z : QuadraticFrequencyIndex =>
      ‖if K < (z.2.1.val : ℕ) then F (quadraticFrequencyValue z) else 0‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hGi
  apply (norm_tsum_le_tsum_norm hpi).trans
  apply (hpi.tsum_le_tsum hp hGi).trans_eq
  apply quadraticFrequencyValue_injective.tsum_eq
  intro h hh
  rw [quadraticFrequencyValue_range]
  intro hz
  apply hh
  simp only [G, hz, Int.natAbs_zero, not_lt_zero, ite_false]

theorem quadratic_schwartz_kernel_tail (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℝ), 0 < Y → ∀ e q K : ℕ,
      ‖∑' z : QuadraticFrequencyIndex,
        if K < (z.2.1.val : ℕ) then
          (jacobiSym ((e : ℤ) * quadraticFrequencyValue z) q : ℂ) *
            ψ ((quadraticFrequencyValue z : ℤ) * Y) else 0‖ ≤
        C / (Y ^ (A + 2) * ((K : ℝ) + 1) ^ A) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_frequency_tail ψ A
  refine ⟨C, hC, ?_⟩
  intro Y hY e q K
  let F : ℤ → ℂ := fun h => (jacobiSym ((e : ℤ) * h) q : ℂ) * ψ ((h : ℝ) * Y)
  have hbase : Summable (fun h : ℤ => ‖ψ ((h : ℝ) * Y)‖) := by
    simpa only [div_inv_eq_mul] using quadratic_scaled_summable ψ (inv_pos.mpr hY)
  have hbound (h : ℤ) : ‖F h‖ ≤ ‖ψ ((h : ℝ) * Y)‖ := by
    have hJ : ‖(jacobiSym ((e : ℤ) * h) q : ℂ)‖ ≤ 1 := by
      rcases jacobiSym.trichotomy ((e : ℤ) * h) q with hh | hh | hh <;> rw [hh] <;> norm_num
    change ‖(jacobiSym ((e : ℤ) * h) q : ℂ) * ψ ((h : ℝ) * Y)‖ ≤ _
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hJ (norm_nonneg _)).trans_eq (one_mul _)
  have hFn : Summable (fun h => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hbase
  have htail : Summable (fun h : ℤ => if K < h.natAbs then ‖ψ ((h : ℝ) * Y)‖ else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hbase
    intro h
    split_ifs <;> simp
  have hFtail : Summable (fun h : ℤ => if K < h.natAbs then ‖F h‖ else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hFn
    intro h
    split_ifs <;> simp
  apply (quadratic_signed_kernel_tail_bound F hFn K).trans
  apply le_trans _ (hc Y hY K)
  apply hFtail.tsum_le_tsum _ htail
  intro h
  split_ifs
  · exact hbound h
  · rfl

end Ostmann

end OAI
