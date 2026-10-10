import OAI.NumberTheory.TwoPoint.Walks.BlockEdgeForm
import OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages

namespace OAI

/-! Normalize an averaged quadratic form and transfer its bound to the
retained prefix, with explicit displacement and boundary errors. -/

namespace TwoPointCorrelations

open Finset

lemma edgeBlockSum_norm_average_le {E : Type*} [Fintype E]
    (r : E → ℕ) (c : E → ℕ → ℂ) (M N : ℕ) :
    ‖((∑ t ∈ range N, edgeBlockSum univ r c M t) / (M : ℂ)) / (N : ℂ)‖ ≤
      uniformAverage (fun t : Fin N => ‖edgeBlockSum univ r c M t.val‖) / M := by
  simp only [norm_div, Complex.norm_natCast]
  calc
    _ ≤ ((∑ t ∈ range N, ‖edgeBlockSum univ r c M t‖) / (M : ℝ)) / N := by
      gcongr
      exact norm_sum_le _ _
    _ = _ := by
      rw [uniformAverage, Fintype.card_fin, Fin.sum_univ_eq_sum_range
        (fun t => ‖edgeBlockSum univ r c M t‖) N]
      ring

theorem block_form_prefix_bound {E : Type*} [Fintype E]
    (r : E → ℕ) (c : E → ℕ → ℂ) (A : ℕ → ℂ)
    (M R N : ℕ) (hM : 0 < M) (hN : 0 < N) (L B D : ℝ)
    (hL : 0 < L) (hD : 0 ≤ D) (hr : ∀ e, r e ≤ R)
    (hrow : ∀ n : ℕ, 0 < n → (∑ e : E, ‖c e n‖) ≤ D)
    (hA : ∀ t, A t = (2 * (L : ℂ)) * edgeBlockSum univ r c M t)
    (havg : uniformAverage (fun t : Fin N => ‖A t.val‖) ≤ B) :
    ‖positivePrefix (fun n => ∑ e : E, c e n) N / (N : ℂ)‖ ≤
      B / (2 * L * M) + (R : ℝ) / M * D + 2 * (M : ℝ) / N * D := by
  have he : uniformAverage (fun t : Fin N => ‖A t.val‖) =
      (2 * L) * uniformAverage (fun t : Fin N => ‖edgeBlockSum univ r c M t.val‖) := by
    simp only [hA, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    unfold uniformAverage
    rw [← mul_sum]
    ring
  have hb : uniformAverage (fun t : Fin N => ‖edgeBlockSum univ r c M t.val‖) ≤ B / (2 * L) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * L)).mpr
    rw [mul_comm, ← he]
    exact havg
  have hprefix := edgeBlockSum_prefix_error univ r c M R N hM hN D hD
    (fun e _ => hr e) hrow
  let Z := ((∑ t ∈ range N, edgeBlockSum univ r c M t) / (M : ℂ)) / (N : ℂ)
  have hZ : ‖Z‖ ≤ B / (2 * L * M) := by
    apply (edgeBlockSum_norm_average_le r c M N).trans
    calc
      _ ≤ (B / (2 * L)) / M := div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)
      _ = _ := by ring
  have ht := norm_sub_le Z
    (Z - positivePrefix (fun n => ∑ e : E, c e n) N / (N : ℂ))
  have hid : Z - (Z - positivePrefix (fun n => ∑ e : E, c e n) N / (N : ℂ)) =
      positivePrefix (fun n => ∑ e : E, c e n) N / (N : ℂ) := by ring
  rw [hid] at ht
  dsimp only [Z] at ht hZ
  linarith

end TwoPointCorrelations

end OAI
