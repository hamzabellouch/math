import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSchwartzTail

namespace OAI

/-! # A finite frequency window with its actual Schwartz remainder -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

 theorem quadratic_schwartz_tail_norm (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 0 < Y → ∀ L : ℕ,
      ‖∑' n : ℤ, if L < n.natAbs then ψ ((n : ℝ) * Y) else 0‖ ≤
        C / (Y ^ (A + 2) * ((L : ℝ) + 1) ^ A) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_frequency_tail ψ A
  refine ⟨C, hC, ?_⟩
  intro Y hY L
  have hs : Summable (fun n : ℤ => ‖ψ ((n : ℝ) * Y)‖) := by
    simpa only [div_inv_eq_mul] using quadratic_scaled_summable ψ (inv_pos.mpr hY)
  have ht : Summable (fun n : ℤ => ‖if L < n.natAbs then ψ ((n : ℝ) * Y) else 0‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
    intro n
    split_ifs <;> simp
  apply (norm_tsum_le_tsum_norm ht).trans
  simpa only [apply_ite, norm_zero] using hc Y hY L

private theorem outside_int_window (n : ℤ) (L : ℕ) :
    n ∉ Finset.Icc (-(L : ℤ)) L ↔ L < n.natAbs := by
  simp only [Finset.mem_Icc, not_and_or]
  omega

 theorem quadratic_frequency_window (ψ : 𝓢(ℝ, ℂ)) {Y : ℝ} (hY : 0 < Y) (L : ℕ) :
    (∑' n : ℤ, if n = 0 then 0 else ψ ((n : ℝ) * Y)) =
      (∑ n ∈ Finset.Icc (-(L : ℤ)) L, if n = 0 then 0 else ψ ((n : ℝ) * Y)) +
      ∑' n : ℤ, if L < n.natAbs then ψ ((n : ℝ) * Y) else 0 := by
  have hs : Summable (fun n : ℤ => ‖ψ ((n : ℝ) * Y)‖) := by
    simpa only [div_inv_eq_mul] using quadratic_scaled_summable ψ (inv_pos.mpr hY)
  have hf : Summable (fun n : ℤ => if n = 0 then 0 else ψ ((n : ℝ) * Y)) := by
    apply Summable.of_norm_bounded hs
    intro n
    split_ifs <;> simp
  have hh := hf.sum_add_tsum_subtype_compl (Finset.Icc (-(L : ℤ)) L)
  have ht := tsum_subtype {n : ℤ | n ∉ Finset.Icc (-(L : ℤ)) L}
    (fun n : ℤ => if n = 0 then 0 else ψ ((n : ℝ) * Y))
  have hh' := (congrArg (fun z : ℂ =>
    (∑ n ∈ Finset.Icc (-(L : ℤ)) L, if n = 0 then 0 else ψ ((n : ℝ) * Y)) + z) ht).symm.trans hh
  simp only [Set.indicator, Set.mem_ofPred_eq] at hh'
  rw [← hh']
  congr 1
  apply tsum_congr
  intro n
  simp only [outside_int_window]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

end Ostmann

end OAI
