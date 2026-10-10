import OAI.NumberTheory.TwoPoint.Bounds.RoughShiftBoundary

namespace OAI

/-! Overlapping blocks recover a positive prefix. The missing terminal
edges cost displacement/block length, and translation costs block/prefix length. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def edgeBlockSum {E : Type*} (edges : Finset E) (r : E → ℕ)
    (c : E → ℕ → ℂ) (M t : ℕ) : ℂ :=
  ∑ i ∈ range M, ∑ e ∈ edges, if i + 1 + r e ≤ M then c e (t + i + 2) else 0

noncomputable def fullBlockSum {E : Type*} (edges : Finset E)
    (c : E → ℕ → ℂ) (M t : ℕ) : ℂ :=
  ∑ i ∈ range M, ∑ e ∈ edges, c e (t + i + 2)

lemma edgeBlockSum_error {E : Type*} (edges : Finset E) (r : E → ℕ)
    (c : E → ℕ → ℂ) (M R t : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hr : ∀ e ∈ edges, r e ≤ R)
    (hc : ∀ n, 0 < n → (∑ e ∈ edges, ‖c e n‖) ≤ D) :
    ‖edgeBlockSum edges r c M t - fullBlockSum edges c M t‖ ≤ R * D := by
  have hterm (i : ℕ) :
      ‖(∑ e ∈ edges, if i + 1 + r e ≤ M then c e (t + i + 2) else 0) -
        ∑ e ∈ edges, c e (t + i + 2)‖ ≤ if M - R ≤ i then D else 0 := by
    by_cases hi : M - R ≤ i
    · rw [ite_eq_left hi, ← sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply le_trans _ (hc (t + i + 2) (by omega))
      apply sum_le_sum
      intro e _
      split_ifs <;> simp
    · rw [ite_eq_right hi]
      have he (e : E) (he : e ∈ edges) : i + 1 + r e ≤ M := by
        have := hr e he
        omega
      have hz : (∑ e ∈ edges, if i + 1 + r e ≤ M then c e (t + i + 2) else 0) =
          ∑ e ∈ edges, c e (t + i + 2) := by
        apply sum_congr rfl
        intro e he'
        rw [ite_eq_left (he e he')]
      simp only [hz, sub_self, norm_zero, le_refl]
  have hfilter : (range M).filter (fun i => M - R ≤ i) = Ico (M - R) M := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  calc
    _ = ‖∑ i ∈ range M,
        ((∑ e ∈ edges, if i + 1 + r e ≤ M then c e (t + i + 2) else 0) -
          ∑ e ∈ edges, c e (t + i + 2))‖ := by rw [sum_sub_distrib]; rfl
    _ ≤ ∑ i ∈ range M, ‖(∑ e ∈ edges,
        if i + 1 + r e ≤ M then c e (t + i + 2) else 0) -
          ∑ e ∈ edges, c e (t + i + 2)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range M, if M - R ≤ i then D else 0 := sum_le_sum (fun i _ => hterm i)
    _ = (M - (M - R) : ℕ) * D := by
      rw [← sum_filter, hfilter]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show M - (M - R) ≤ R by omega)) hD

lemma fullBlockSum_prefix_identity {E : Type*} (edges : Finset E)
    (c : E → ℕ → ℂ) (M N : ℕ) :
    (M : ℂ)⁻¹ * ∑ t ∈ range N, fullBlockSum edges c M t =
      translatedPrefixAverage (fun n => ∑ e ∈ edges, c e n) N M := by
  unfold fullBlockSum translatedPrefixAverage positivePrefix
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro t _
  rw [show t + i + 2 = t + 1 + (i + 1) by omega]

lemma edgeBlockSum_prefix_error {E : Type*} (edges : Finset E) (r : E → ℕ)
    (c : E → ℕ → ℂ) (M R N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (D : ℝ) (hD : 0 ≤ D) (hr : ∀ e ∈ edges, r e ≤ R)
    (hc : ∀ n, 0 < n → (∑ e ∈ edges, ‖c e n‖) ≤ D) :
    ‖((∑ t ∈ range N, edgeBlockSum edges r c M t) / (M : ℂ)) / (N : ℂ) -
        positivePrefix (fun n => ∑ e ∈ edges, c e n) N / (N : ℂ)‖ ≤
      (R : ℝ) / M * D + 2 * (M : ℝ) / N * D := by
  let F := fun n => ∑ e ∈ edges, c e n
  let T := translatedPrefixAverage F N M
  have htranslate := norm_normalized_translation_error F N M hN hM D hD
    (fun n hn => (norm_sum_le _ _).trans (hc n hn))
  have hblock : ‖((∑ t ∈ range N, edgeBlockSum edges r c M t) / (M : ℂ)) /
      (N : ℂ) - T / (N : ℂ)‖ ≤ (R : ℝ) / M * D := by
    have heq : ((∑ t ∈ range N, edgeBlockSum edges r c M t) / (M : ℂ)) /
        (N : ℂ) - T / (N : ℂ) =
        ((∑ t ∈ range N, (edgeBlockSum edges r c M t - fullBlockSum edges c M t)) /
          (M : ℂ)) / (N : ℂ) := by
      dsimp [T, F]
      rw [← fullBlockSum_prefix_identity edges c M N, sum_sub_distrib]
      ring
    rw [heq, norm_div, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    have hs : ‖∑ t ∈ range N, (edgeBlockSum edges r c M t - fullBlockSum edges c M t)‖ ≤
        (N : ℝ) * ((R : ℝ) * D) := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _t ∈ range N, (R : ℝ) * D :=
          sum_le_sum (fun t _ => edgeBlockSum_error edges r c M R t D hD hr hc)
        _ = _ := by simp
    have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    calc
      _ ≤ ((N : ℝ) * ((R : ℝ) * D) / M) / N :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hs hMr.le) hNr.le
      _ = _ := by field_simp
  calc
    _ ≤ ‖((∑ t ∈ range N, edgeBlockSum edges r c M t) / (M : ℂ)) /
        (N : ℂ) - T / (N : ℂ)‖ + ‖(T - positivePrefix F N) / (N : ℂ)‖ := by
      have heq : ((∑ t ∈ range N, edgeBlockSum edges r c M t) / (M : ℂ)) /
          (N : ℂ) - positivePrefix F N / (N : ℂ) =
          (((∑ t ∈ range N, edgeBlockSum edges r c M t) / (M : ℂ)) /
            (N : ℂ) - T / (N : ℂ)) + (T - positivePrefix F N) / (N : ℂ) := by ring
      rw [heq]
      exact norm_add_le _ _
    _ ≤ _ := add_le_add hblock htranslate

end TwoPointCorrelations

end OAI
