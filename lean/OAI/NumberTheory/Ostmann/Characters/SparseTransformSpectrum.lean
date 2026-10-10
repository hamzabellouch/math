import OAI.NumberTheory.Ostmann.Characters.NormalizedResidueIndicator

namespace OAI

/-! # Concentration of a small-L1 normalized additive transform

This is the finite argument (5.7), before the contracting kernel in
Proposition 5.1. It requires no analytic input.
-/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def largeTransformSpectrum {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) : Finset (ZMod p) := Finset.univ.filter fun b => 1 < ‖g b‖

theorem largeTransformSpectrum_zero_not_mem {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : g 0 = 0) : 0 ∉ largeTransformSpectrum g := by
  simp [largeTransformSpectrum, hg]

theorem largeTransformSpectrum_neg {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : ∀ b, g (-b) = conj (g b)) (b : ZMod p) :
    -b ∈ largeTransformSpectrum g ↔ b ∈ largeTransformSpectrum g := by
  simp only [largeTransformSpectrum, Finset.mem_filter, Finset.mem_univ, true_and,
    hg, Complex.norm_conj]

/-- The large coefficients occupy a small set and retain almost all energy. -/
theorem largeTransformSpectrum_bounds {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (δ : ℝ)
    (hL1 : (∑ b, ‖g b‖) ≤ δ * p) (hL2 : (∑ b, ‖g b‖ ^ 2) = p) :
    ((largeTransformSpectrum g).card : ℝ) ≤ δ * p ∧
      (1 - δ) * p ≤ ∑ b ∈ largeTransformSpectrum g, ‖g b‖ ^ 2 := by
  let E := largeTransformSpectrum g
  have hcard : (E.card : ℝ) ≤ ∑ b ∈ E, ‖g b‖ := by
    calc
      _ = ∑ _b ∈ E, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun b hb =>
        (Finset.mem_filter.mp hb).2.le
  have hL1E : (∑ b ∈ E, ‖g b‖) ≤ ∑ b, ‖g b‖ :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)
  refine ⟨hcard.trans (hL1E.trans hL1), ?_⟩
  have hsmall : (∑ b ∈ Finset.univ \ E, ‖g b‖ ^ 2) ≤ δ * p := by
    calc
      _ ≤ ∑ b ∈ Finset.univ \ E, ‖g b‖ := by
        apply Finset.sum_le_sum
        intro b hb
        have hn : ‖g b‖ ≤ 1 := by
          have hnot := (Finset.mem_sdiff.mp hb).2
          simpa only [E, largeTransformSpectrum, Finset.mem_filter, Finset.mem_univ,
            true_and, not_lt] using hnot
        nlinarith [norm_nonneg (g b)]
      _ ≤ ∑ b, ‖g b‖ := Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)
      _ ≤ _ := hL1
  have hsplit : (∑ b ∈ E, ‖g b‖ ^ 2) +
      (∑ b ∈ Finset.univ \ E, ‖g b‖ ^ 2) = p := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ E), hL2]
    ring
  linarith

/-- The exact normalized residue transform satisfies the sparse-spectrum
conclusions used in Section 5 whenever its probability L1 norm is small. -/
theorem normalizedResidueTransform_sparse {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (ε δ : ℝ) (hδ : δ ≤ ε) (hδsq : δ ≤ ε ^ 2)
    (hL1 : (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖ ≤ δ) :
    let E := largeTransformSpectrum (normalizedResidueTransform S)
    0 ∉ E ∧ (∀ b, -b ∈ E ↔ b ∈ E) ∧
      (E.card : ℝ) ≤ ε * p ∧
      (1 - ε ^ 2) * p ≤ ∑ b ∈ E, ‖normalizedResidueTransform S b‖ ^ 2 := by
  intro E
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hmass : (∑ b, ‖normalizedResidueTransform S b‖) ≤ δ * p := by
    have hh := mul_le_mul_of_nonneg_left hL1 hp.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul, mul_comm (p : ℝ) δ] using hh
  obtain ⟨hc, he⟩ := largeTransformSpectrum_bounds _ δ hmass
    (normalizedResidueTransform_energy S hS hSp)
  refine ⟨largeTransformSpectrum_zero_not_mem _ (normalizedResidueTransform_zero S),
    largeTransformSpectrum_neg _ (normalizedResidueTransform_neg S),
    hc.trans (mul_le_mul_of_nonneg_right hδ hp.le), ?_⟩
  exact (mul_le_mul_of_nonneg_right (by linarith : 1 - ε ^ 2 ≤ 1 - δ) hp.le).trans he

end Ostmann

end OAI
