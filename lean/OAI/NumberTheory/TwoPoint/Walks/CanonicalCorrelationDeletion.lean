import OAI.NumberTheory.TwoPoint.Walks.RetainedEligibility
import OAI.NumberTheory.TwoPoint.Walks.CanonicalBinSummation
import OAI.NumberTheory.TwoPoint.Walks.CanonicalShiftedDeletion

namespace OAI

/-! The literal uncut bin correlation differs from the spectral test
by the two canonical endpoint deletion costs. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def canonicalUncutPrefix (h l b : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (N : ℕ) : ℂ :=
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let R := boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊
  uncutPrimePrefix P R eligible h (progressionEdgeGate h l b) N

lemma canonical_uncut_sub_retained_prefix (h l b : ℕ) (E : Finset ℕ)
    (W L η : ℝ) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (c : ℕ → ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (j : ℤ) (N : ℕ)
    (hbin : ∀ d q, eligible j d q → actualPaddingBin η (c d) j q) :
    let J := primeSupplyCount W L
    let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
    let Q := paddingPrimeSupply E L
    let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
    let bad := fun k n => ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
      (fun d q => (d, q) ∈ (canonicalTraceFamily h E W L (eligible k) hL hW hE).pairs) n
    ‖canonicalUncutPrefix h l b E W L (eligible j) N -
      canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE N‖ ≤
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
  have hcongr := retainedPrimePrefix_congr_eligible P hp hd R Q actualPaddingCoefficient
    active (eligible j) L (Real.exp (4 * J)) W (fun _ => actualPaddingDegreeCut Q L)
    h (progressionEdgeGate h l b) (fun z => ¬bad j z) N
    (fun d hd q hq => canonicalTraceFamily_pair_on_pool h E W L (eligible j) hL hW hE d q hd hq)
  change ‖uncutPrimePrefix P R (eligible j) h (progressionEdgeGate h l b) N -
    retainedPrimePrefix P R Q actualPaddingCoefficient active L (Real.exp (4 * J)) W
      (fun _ => actualPaddingDegreeCut Q L) h (progressionEdgeGate h l b)
      (fun z => ¬bad j z) N‖ ≤ _
  rw [hcongr]
  exact uncut_sub_retained_prefix_le P hp hd R Q η c L (Real.exp (4 * J)) W
    eligible h (progressionEdgeGate h l b) bad j N (fun d _ q _ => hbin d q)

lemma prefix_start_one_add (n : ℕ) : (1 : ℤ) + n = ((n + 1 : ℕ) : ℤ) := by
  push_cast
  ring

lemma canonical_weighted_correlation_deletion (h l b : ℕ) (E : Finset ℕ)
    (W L η : ℝ) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (bins : Finset ℤ)
    (c : ℕ → ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (N : ℤ → ℕ) (v : ℤ → ℂ)
    (hbin : ∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (c d) j q)
    (hv : ∀ j ∈ bins, ‖v j‖ ≤ 1) :
    ‖(∑ j ∈ bins, v j * canonicalUncutPrefix h l b E W L (eligible j) (N j)) -
      (∑ j ∈ bins, v j * canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j))‖ ≤
      canonicalShiftedSourceDeletion h E W L η (Real.exp (4 * primeSupplyCount W L))
        hL hW hE bins c eligible (fun _ _ _ => 0) (fun _ => 1) N +
      canonicalShiftedSourceDeletion h E W L η (Real.exp (4 * primeSupplyCount W L))
        hL hW hE bins c eligible (fun _ d q => (h * q * d : ℕ)) (fun _ => 1) N := by
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ bins, ‖canonicalUncutPrefix h l b E W L (eligible j) (N j) -
        canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j)‖ := by
      apply sum_le_sum
      intro j hj
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hv j hj) (norm_nonneg _)
    _ ≤ ∑ j ∈ bins, _ := sum_le_sum (fun j hj =>
      canonical_uncut_sub_retained_prefix h l b E W L η hL hW hE c eligible j (N j) (hbin j hj))
    _ = _ := by
      simp only [canonicalShiftedSourceDeletion, Nat.cast_one, prefix_start_one_add,
        sum_add_distrib, add_zero]

end TwoPointCorrelations

end OAI
