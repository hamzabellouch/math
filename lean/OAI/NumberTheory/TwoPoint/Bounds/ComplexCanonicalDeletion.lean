import OAI.NumberTheory.TwoPoint.Bounds.ComplexBinSummation
import OAI.NumberTheory.TwoPoint.Bounds.ComplexDeletionPrefix
import OAI.NumberTheory.TwoPoint.Walks.CanonicalCorrelationDeletion

namespace OAI

/-! The actual complex uncut correlation is controlled by the existing two endpoint costs. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def canonicalComplexUncutPrefix (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (F G : ℤ → ℂ) (N : ℕ) : ℂ :=
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let R := boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊
  untwistedUncutPrefix P R eligible h (fun _ _ _ => True) F G N

lemma canonical_complex_uncut_sub_retained_prefix (h : ℕ) (E : Finset ℕ)
    (W L η : ℝ) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (c : ℕ → ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (j : ℤ) (N : ℕ)
    (F G : ℤ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 1) (hG : ∀ n, ‖G n‖ ≤ 1)
    (hbin : ∀ d q, eligible j d q → actualPaddingBin η (c d) j q) :
    let J := primeSupplyCount W L
    let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
    let Q := paddingPrimeSupply E L
    let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
    let bad := fun k n => ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
      (fun d q => (d, q) ∈ (canonicalTraceFamily h E W L (eligible k) hL hW hE).pairs) n
    ‖canonicalComplexUncutPrefix h E W L (eligible j) F G N -
      canonicalComplexPrefix h E W L (eligible j) hL hW hE F G N‖ ≤
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L (Real.exp (4 * J)) W eligible bad j d q ((x.val + 1 : ℕ) : ℤ))) +
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L (Real.exp (4 * J)) W eligible bad j d q
            (((x.val + 1 : ℕ) : ℤ) + (h * q * d : ℕ)))) := by
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  let bad := fun k n => ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ (canonicalTraceFamily h E W L (eligible k) hL hW hE).pairs) n
  let active := fun d q => (d, q) ∈ (canonicalTraceFamily h E W L (eligible j) hL hW hE).pairs
  have hp : ∀ i, ∀ p ∈ P i, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ i k, k ≠ i → Disjoint (P i) (P k) := centeredPrimeBands_disjoint _ _ _ _
    (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hW)
  have hcongr := untwistedRetainedPrefix_congr_eligible P R Q actualPaddingCoefficient
    active (eligible j) L (Real.exp (4 * J)) W (fun _ => actualPaddingDegreeCut Q L)
    h (fun _ _ _ => True) (fun z => ¬bad j z) F G N
    (fun d hd q hq => canonicalTraceFamily_pair_on_pool h E W L (eligible j) hL hW hE d q hd hq)
  change ‖untwistedUncutPrefix P R (eligible j) h (fun _ _ _ => True) F G N -
    retainedComplexPrefix P R Q actualPaddingCoefficient active L (Real.exp (4 * J)) W
      (fun _ => actualPaddingDegreeCut Q L) h (fun _ _ _ => True)
      (fun z => ¬bad j z) F G N‖ ≤ _
  rw [retainedComplexPrefix_eq_numerical P hp hd R Q actualPaddingCoefficient active
    L (Real.exp (4 * J)) W (fun _ => actualPaddingDegreeCut Q L) h (fun _ _ _ => True)
    (fun z => ¬bad j z) F G N (by linarith), hcongr]
  exact complex_uncut_sub_retained_prefix_le P hp hd R Q η c L (Real.exp (4 * J)) W
    eligible h (fun _ _ _ => True) bad j N F G hF hG (fun d _ q _ => hbin d q)

lemma canonical_complex_weighted_correlation_deletion (h : ℕ) (E : Finset ℕ)
    (W L η : ℝ) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (bins : Finset ℤ)
    (c : ℕ → ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (N : ℤ → ℕ) (v : ℤ → ℂ)
    (F G : ℤ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 1) (hG : ∀ n, ‖G n‖ ≤ 1)
    (hbin : ∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (c d) j q)
    (hv : ∀ j ∈ bins, ‖v j‖ ≤ 1) :
    ‖(∑ j ∈ bins, v j * canonicalComplexUncutPrefix h E W L (eligible j) F G (N j)) -
      (∑ j ∈ bins, v j * canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j))‖ ≤
      canonicalShiftedSourceDeletion h E W L η (Real.exp (4 * primeSupplyCount W L))
        hL hW hE bins c eligible (fun _ _ _ => 0) (fun _ => 1) N +
      canonicalShiftedSourceDeletion h E W L η (Real.exp (4 * primeSupplyCount W L))
        hL hW hE bins c eligible (fun _ d q => (h * q * d : ℕ)) (fun _ => 1) N := by
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ bins, ‖canonicalComplexUncutPrefix h E W L (eligible j) F G (N j) -
        canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j)‖ := by
      apply sum_le_sum
      intro j hj
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hv j hj) (norm_nonneg _)
    _ ≤ ∑ j ∈ bins, _ := sum_le_sum (fun j hj =>
      canonical_complex_uncut_sub_retained_prefix h E W L η hL hW hE c eligible j (N j) F G hF hG (hbin j hj))
    _ = _ := by
      simp only [canonicalShiftedSourceDeletion, Nat.cast_one, prefix_start_one_add,
        sum_add_distrib, add_zero]


end TwoPointCorrelations

end OAI
