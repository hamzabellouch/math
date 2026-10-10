import OAI.NumberTheory.TwoPoint.Fourier.MinorArcWindowProduct
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcOriginCount
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcKernelSymmetry

namespace OAI

/-! Summing a fixed prime quadruple over its possible interval origins. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical ComplexConjugate

lemma minor_arc_origin_kernel_sum (X M A B C D H : ℕ) (hA : 0 < A)
    (hB0 : 0 < B) (hC0 : 0 < C) (hD0 : 0 < D)
    (hB : B ≤ 2 * A) (hC : C ≤ 2 * A) (hD : D ≤ 2 * A)
    (z₁ z₂ z₃ z₄ : ℕ → ℂ) (hz₁ : ∀ k, ‖z₁ k‖ ≤ 1) (hz₂ : ∀ k, ‖z₂ k‖ ≤ 1)
    (hz₃ : ∀ k, ‖z₃ k‖ ≤ 1) (hz₄ : ∀ k, ‖z₄ k‖ ≤ 1)
    (β₁ β₂ β₃ β₄ V : ℝ) (hV : (H : ℝ) / A + 1 ≤ V) :
    (∑ k ∈ range X, ∑ l ∈ range X, ∑ r ∈ range X, ∑ s ∈ range X,
      ‖∑ m ∈ range M,
        minorArcWindowTerm M A k H (z₁ k) β₁ m * minorArcWindowTerm M B l H (z₂ l) β₂ m *
          conj (minorArcWindowTerm M C r H (z₃ r) β₃ m) *
          conj (minorArcWindowTerm M D s H (z₄ s) β₄ m)‖) ≤
      (X * (3 * H + 1) ^ 3 : ℕ) * minorArcGeometricBound V (β₁ + β₂ - β₃ - β₄) := by
  let Q := ((range X) ×ˢ (range X)) ×ˢ ((range X) ×ˢ (range X))
  let S := fun v : (ℕ × ℕ) × (ℕ × ℕ) =>
    (minorArcWindowInterval M A v.1.1 H ∩ minorArcWindowInterval M B v.1.2 H) ∩
      (minorArcWindowInterval M C v.2.1 H ∩ minorArcWindowInterval M D v.2.2 H)
  let T := Q.filter (fun v => (S v).Nonempty)
  let K := minorArcGeometricBound V (β₁ + β₂ - β₃ - β₄)
  have hV0 : 0 ≤ V := by
    have h : 0 ≤ (H : ℝ) / A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  have hK : 0 ≤ K := minor_arc_geometric_nonneg hV0 _
  have hcard : T.card ≤ X * (3 * H + 1) ^ 3 := by
    apply minor_arc_origin_quadruples X H A B C D hA hB hC hD T
    rintro ⟨⟨k, l⟩, ⟨r, s⟩⟩ hv
    obtain ⟨hvQ, m, hm⟩ := mem_filter.mp hv
    have hkX := (mem_product.mp (mem_product.mp hvQ).1).1
    obtain ⟨hm₁, hm₂⟩ := mem_inter.mp hm
    obtain ⟨hmA, hmB⟩ := mem_inter.mp hm₁
    obtain ⟨hmC, hmD⟩ := mem_inter.mp hm₂
    exact ⟨mem_range.mp hkX, m,
      ((mem_minorArcWindowInterval M A k H m hA).mp hmA).2,
      ((mem_minorArcWindowInterval M B l H m hB0).mp hmB).2,
      ((mem_minorArcWindowInterval M C r H m hC0).mp hmC).2,
      ((mem_minorArcWindowInterval M D s H m hD0).mp hmD).2⟩
  have hz (k l r s : ℕ) : ‖z₁ k * z₂ l * conj (z₃ r) * conj (z₄ s)‖ ≤ 1 := by
    simp only [norm_mul, Complex.norm_conj]
    calc
      ‖z₁ k‖ * ‖z₂ l‖ * ‖z₃ r‖ * ‖z₄ s‖ ≤ 1 * 1 * 1 * 1 := by
        gcongr <;> first | exact hz₁ _ | exact hz₂ _ | exact hz₃ _ | exact hz₄ _
      _ = 1 := by norm_num
  calc
    _ ≤ ∑ k ∈ range X, ∑ l ∈ range X, ∑ r ∈ range X, ∑ s ∈ range X,
        if (S ((k, l), (r, s))).Nonempty then K else 0 := by
      repeat' apply sum_le_sum fun _ _ => ?_
      exact minor_arc_window_product_support M A B C D _ _ _ _ H hA _ _ _ _
        β₁ β₂ β₃ β₄ V (hz _ _ _ _) hV
    _ = ∑ v ∈ Q, if (S v).Nonempty then K else 0 := by
      simp only [Q, sum_product]
    _ = (T.card : ℝ) * K := by
      rw [← sum_filter]
      simp only [T, sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr hcard) hK

end TwoPointCorrelations

end OAI
