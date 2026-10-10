import OAI.NumberTheory.TwoPoint.Walks.BlockEndpointSum

namespace OAI

/-! The finite directed matrix form is the overlapping edge-block sum
used in the prefix comparison, with no residual multiplicity assumption. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem directed_block_form_eq {E : Type*} [Fintype E] (r : E → ℕ)
    (F : E → ℤ → ℤ → ℂ)
    (hsupport : ∀ (e : E) (n m : ℤ), m ≠ n + r e → F e n m = 0) (M t : ℕ) :
    (∑ e : E, ∑ i : Fin M, ∑ j : Fin M,
      F e ((i.val : ℤ) + (t + 2 : ℕ)) ((j.val : ℤ) + (t + 2 : ℕ))) =
      edgeBlockSum univ r (fun e n => F e n ((n : ℤ) + r e)) M t := by
  let g (i : ℕ) := ∑ e : E, if i + r e < M then
    F e ((i : ℤ) + (t + 2 : ℕ)) ((i : ℤ) + (t + 2 : ℕ) + r e) else 0
  calc
    _ = ∑ i : Fin M, ∑ e : E, ∑ j : Fin M,
        F e ((i.val : ℤ) + (t + 2 : ℕ)) ((j.val : ℤ) + (t + 2 : ℕ)) := sum_comm
    _ = ∑ i : Fin M, g i.val := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro e _
      exact block_supported_edge_sum M (r e) (t + 2 : ℕ) (F e) (hsupport e) i
    _ = ∑ i ∈ range M, g i := Fin.sum_univ_eq_sum_range g M
    _ = _ := by
      unfold edgeBlockSum g
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro e _
      have he : i + r e < M ↔ i + 1 + r e ≤ M := by omega
      simp only [he, Nat.cast_add, Nat.cast_ofNat]
      simp only [add_assoc, add_left_comm, add_comm]

theorem directed_block_form_prefix_error {E : Type*} [Fintype E]
    (r : E → ℕ) (F : E → ℤ → ℤ → ℂ)
    (hsupport : ∀ (e : E) (n m : ℤ), m ≠ n + r e → F e n m = 0)
    (M R N : ℕ) (hM : 0 < M) (hN : 0 < N) (D : ℝ) (hD : 0 ≤ D)
    (hr : ∀ e, r e ≤ R)
    (hrow : ∀ n : ℕ, 0 < n → (∑ e : E, ‖F e n ((n : ℤ) + r e)‖) ≤ D) :
    ‖((∑ t ∈ range N, ∑ e : E, ∑ i : Fin M, ∑ j : Fin M,
        F e ((i.val : ℤ) + (t + 2 : ℕ)) ((j.val : ℤ) + (t + 2 : ℕ))) / (M : ℂ)) / (N : ℂ) -
      positivePrefix (fun n => ∑ e : E, F e n ((n : ℤ) + r e)) N / (N : ℂ)‖ ≤
        (R : ℝ) / M * D + 2 * (M : ℝ) / N * D := by
  have hb := edgeBlockSum_prefix_error univ r (fun e n => F e n ((n : ℤ) + r e))
    M R N hM hN D hD (fun e _ => hr e) hrow
  simpa only [directed_block_form_eq r F hsupport] using hb

end TwoPointCorrelations

end OAI
