import OAI.NumberTheory.TwoPoint.Walks.SelectedPairBins
import OAI.NumberTheory.TwoPoint.Bounds.BinCutoffGeometry

namespace OAI

/-! A numerical phase selection gives an admissible graph eligibility in each
actual logarithmic bin, including the padding degree restriction. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def selectedPairBin (η : ℝ) (A : Finset (ℕ × ℕ))
    (j : ℤ) (d q : ℕ) : Prop :=
  (d, q) ∈ A ∧ paddingBin η 0 (Real.log (d * q : ℕ)) = j

lemma selectedPairBin_properties (D Q : Finset ℕ) (hD : ∀ d ∈ D, 0 < d)
    (hQ : ∀ p ∈ Q, p.Prime) (A : Finset (ℕ × ℕ))
    (L η : ℝ) (hη : 0 < η)
    (hA : A ⊆ eligibleComplexPairs D Q (PaddingPairEligible L η))
    {j : ℤ} {d q : ℕ} (he : selectedPairBin η A j d q) :
    0 < d ∧ 0 < q ∧ PaddingPairEligible L η d q ∧
      actualPaddingBin η (Real.log d) j q := by
  have hm := mem_filter.mp (hA he.1)
  have hd := (mem_product.mp hm.1).1
  have hq := (mem_product.mp hm.1).2
  have hdp := hD d hd
  have hqp := retainedPrimeDivisor_pos Q hQ hq
  refine ⟨hdp, hqp, hm.2, ?_⟩
  have hh := (paddingBin_eq_iff η 0 (Real.log (d * q : ℕ)) j hη).mp he.2
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdp.ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqp.ne'
  simpa only [actualPaddingBin, Nat.cast_mul, Real.log_mul hd0 hq0, add_zero,
    add_comm, zero_add] using hh

lemma selectedPairBin_index (D Q : Finset ℕ) (A : Finset (ℕ × ℕ)) (L η : ℝ)
    (hA : A ⊆ eligibleComplexPairs D Q (PaddingPairEligible L η))
    {dq : ℕ × ℕ} (hdq : dq ∈ A) :
    paddingBin η 0 (Real.log (dq.1 * dq.2 : ℕ)) ∈ paddingBinIndices L η :=
  (mem_filter.mp (hA hdq)).2.2

lemma selected_pairs_bounded_padding (D Q : Finset ℕ) (A : Finset (ℕ × ℕ))
    (L η : ℝ) (hL : 1 ≤ L)
    (hA : A ⊆ eligibleComplexPairs D Q (PaddingPairEligible L η)) :
    A ⊆ D ×ˢ boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊ := by
  intro dq hdq
  have hm := mem_filter.mp (hA hdq)
  obtain ⟨hd, hq⟩ := mem_product.mp hm.1
  apply mem_product.mpr
  refine ⟨hd, mem_filter.mpr ⟨hq, ?_⟩⟩
  exact (Nat.le_floor_iff (mul_nonneg (by norm_num) (Real.log_nonneg hL))).mpr hm.2.1

end TwoPointCorrelations

end OAI
