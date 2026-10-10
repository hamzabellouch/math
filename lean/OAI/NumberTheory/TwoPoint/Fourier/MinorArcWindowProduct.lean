import OAI.NumberTheory.TwoPoint.Fourier.MinorArcWindowInterval
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcPrimeFourth

namespace OAI

/-! One term of the fourth expansion of a weighted short-window sum. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical ComplexConjugate

noncomputable def minorArcWindowTerm (M A k H : ℕ) (z : ℂ) (β : ℝ) (m : ℕ) : ℂ :=
  if m ∈ minorArcWindowInterval M A k H then z * additiveCharacter β m else 0

lemma minor_arc_window_product (M A B C D k l r s H : ℕ)
    (hA : 0 < A) (z₁ z₂ z₃ z₄ : ℂ) (β₁ β₂ β₃ β₄ : ℝ) :
    (∑ m ∈ range M,
      minorArcWindowTerm M A k H z₁ β₁ m * minorArcWindowTerm M B l H z₂ β₂ m *
        conj (minorArcWindowTerm M C r H z₃ β₃ m) *
        conj (minorArcWindowTerm M D s H z₄ β₄ m)) =
      (z₁ * z₂ * conj z₃ * conj z₄) *
        ∑ m ∈ (minorArcWindowInterval M A k H ∩ minorArcWindowInterval M B l H) ∩
          (minorArcWindowInterval M C r H ∩ minorArcWindowInterval M D s H),
          additiveCharacter (β₁ + β₂ - β₃ - β₄) m := by
  let S := (minorArcWindowInterval M A k H ∩ minorArcWindowInterval M B l H) ∩
    (minorArcWindowInterval M C r H ∩ minorArcWindowInterval M D s H)
  let z := z₁ * z₂ * conj z₃ * conj z₄
  have hphase (m : ℕ) :
      additiveCharacter β₁ m * additiveCharacter β₂ m *
        conj (additiveCharacter β₃ m) * conj (additiveCharacter β₄ m) =
      additiveCharacter (β₁ + β₂ - β₃ - β₄) m := by
    simpa only [one_mul] using minor_arc_phase_four 1 β₁ β₂ β₃ β₄ m
  have he (m : ℕ) :
      minorArcWindowTerm M A k H z₁ β₁ m * minorArcWindowTerm M B l H z₂ β₂ m *
        conj (minorArcWindowTerm M C r H z₃ β₃ m) *
        conj (minorArcWindowTerm M D s H z₄ β₄ m) =
      if m ∈ S then z * additiveCharacter (β₁ + β₂ - β₃ - β₄) m else 0 := by
    by_cases ha : m ∈ minorArcWindowInterval M A k H
    · by_cases hb : m ∈ minorArcWindowInterval M B l H
      · by_cases hc : m ∈ minorArcWindowInterval M C r H
        · by_cases hd : m ∈ minorArcWindowInterval M D s H
          · simp only [minorArcWindowTerm, ha, hb, hc, hd, ite_true, S, mem_inter,
              and_self, map_mul, z]
            rw [← hphase]
            ring
          · simp [minorArcWindowTerm, S, ha, hb, hc, hd]
        · simp [minorArcWindowTerm, S, ha, hb, hc]
      · simp [minorArcWindowTerm, S, ha, hb]
    · simp [minorArcWindowTerm, S, ha]
  have hsub : S ⊆ range M := by
    intro m hm
    exact mem_range.mpr ((mem_minorArcWindowInterval M A k H m hA).mp
      (mem_inter.mp (mem_inter.mp hm).1).1).1
  have hfilt : (range M).filter (fun m => m ∈ S) = S := by
    ext m
    simp only [mem_filter]
    exact ⟨And.right, fun hm => ⟨hsub hm, hm⟩⟩
  simp_rw [he]
  rw [← sum_filter, hfilt, mul_sum]

lemma minor_arc_window_product_bound (M A B C D k l r s H : ℕ)
    (hA : 0 < A) (z₁ z₂ z₃ z₄ : ℂ) (β₁ β₂ β₃ β₄ V : ℝ)
    (hz : ‖z₁ * z₂ * conj z₃ * conj z₄‖ ≤ 1)
    (hV : (H : ℝ) / A + 1 ≤ V) :
    ‖∑ m ∈ range M,
      minorArcWindowTerm M A k H z₁ β₁ m * minorArcWindowTerm M B l H z₂ β₂ m *
        conj (minorArcWindowTerm M C r H z₃ β₃ m) *
        conj (minorArcWindowTerm M D s H z₄ β₄ m)‖ ≤
      minorArcGeometricBound V (β₁ + β₂ - β₃ - β₄) := by
  rw [minor_arc_window_product M A B C D k l r s H hA, norm_mul]
  calc
    _ ≤ 1 * ‖∑ m ∈ (minorArcWindowInterval M A k H ∩ minorArcWindowInterval M B l H) ∩
        (minorArcWindowInterval M C r H ∩ minorArcWindowInterval M D s H),
        additiveCharacter (β₁ + β₂ - β₃ - β₄) m‖ :=
      mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact (minor_arc_four_window_kernel M A B C D k l r s H hA _).trans
        (minor_arc_geometric_mono hV _)

lemma minor_arc_window_product_support (M A B C D k l r s H : ℕ)
    (hA : 0 < A) (z₁ z₂ z₃ z₄ : ℂ) (β₁ β₂ β₃ β₄ V : ℝ)
    (hz : ‖z₁ * z₂ * conj z₃ * conj z₄‖ ≤ 1)
    (hV : (H : ℝ) / A + 1 ≤ V) :
    ‖∑ m ∈ range M,
      minorArcWindowTerm M A k H z₁ β₁ m * minorArcWindowTerm M B l H z₂ β₂ m *
        conj (minorArcWindowTerm M C r H z₃ β₃ m) *
        conj (minorArcWindowTerm M D s H z₄ β₄ m)‖ ≤
      if ((minorArcWindowInterval M A k H ∩ minorArcWindowInterval M B l H) ∩
          (minorArcWindowInterval M C r H ∩ minorArcWindowInterval M D s H)).Nonempty
      then minorArcGeometricBound V (β₁ + β₂ - β₃ - β₄) else 0 := by
  split_ifs with hs
  · exact minor_arc_window_product_bound M A B C D k l r s H hA
      z₁ z₂ z₃ z₄ β₁ β₂ β₃ β₄ V hz hV
  · have hempty := not_nonempty_iff_eq_empty.mp hs
    rw [minor_arc_window_product M A B C D k l r s H hA, hempty]
    simp

end TwoPointCorrelations

end OAI
