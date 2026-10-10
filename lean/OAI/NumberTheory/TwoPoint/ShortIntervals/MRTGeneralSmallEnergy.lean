import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralTypical
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCofactorMean

namespace OAI

/-! The first-small-band energy bound for ordinary multiplicative
functions, including the explicit prime-square extraction error. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_general_typical_small_prime_energy {ι κ : Type*} [DecidableEq κ]
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P j, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower (bin p) ≤ p ∧ (p : ℝ) ≤ δ * lower (bin p))
    (hlow : ∀ k ∈ K, 1 ≤ lower k) (hupper : ∀ k ∈ K, 2 ≤ (N : ℝ) / lower k)
    (F : ℕ → ℂ)
    (hF : Multiplicative F)
    (hFb : OneBounded F) {T : ℝ} (hT : 0 < T)
    (E : Set ℝ) (hE : E ⊆ Set.Ioc (-T) T) (A : κ → ℝ)
    (hsmall : ∀ k ∈ K, ∀ t ∈ E,
      ‖mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
        (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖ ≤ A k) :
    (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖ ^ 2) ≤
      2816 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) +
      64 * Real.exp 1 * (K.card : ℝ) *
        ∑ k ∈ K, (A k) ^ 2 * (T * lower k / (N : ℝ) + 1) := by
  let B := mrtTypicalCoefficient (J.erase j) P F
  let Q : κ → ℝ → ℂ := fun k =>
    mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
      (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ))
  let R : κ → ℝ → ℂ := fun k => mrtCofactorPolynomial (P j) B N (lower k)
  let D := mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N
  let G : ℝ → ℂ := fun t => ∑ k ∈ K, Q k t * R k t
  have hB : OneBounded B := mrtTypicalCoefficient_oneBounded _ _ _ hFb
  have hR (k : κ) (_hk : k ∈ K) : Continuous (R k) :=
    mrtCofactorPolynomial_continuous (P j) B N (lower k)
  have hD : Continuous D := mrtExponentialPolynomial_continuous _ _ _
  have hG : Continuous G := continuous_finsetSum K (fun k hk =>
    (mrtExponentialPolynomial_continuous _ _ _).mul (hR k hk))
  have hg := mrt_restricted_product_sum_energy K Q R hR A hT.le hE hsmall
  have hg' : (∫ t in E, ‖G t‖ ^ 2) ≤
      32 * Real.exp 1 * (K.card : ℝ) *
        ∑ k ∈ K, (A k) ^ 2 * (T * lower k / (N : ℝ) + 1) := by
    change (∫ t in E, ‖∑ k ∈ K, Q k t * R k t‖ ^ 2) ≤ _
    apply hg.trans
    calc
      _ ≤ (K.card : ℝ) * ∑ k ∈ K, (A k) ^ 2 *
          (32 * Real.exp 1 * (T * lower k / (N : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (mrt_cofactor_mean_square (P j) B hB N (hlow k hk) (hupper k hk) hT)
          (sq_nonneg _)
      _ = _ := by
        simp only [mul_sum]
        apply sum_congr rfl
        intro k _
        ring
  have herr := mrt_typical_general_prime_mean_square J P hP hdis hj
    (fun p => lower (bin p)) hN hδ hδ2 hL F hF hFb hT
  simp_rw [mrt_extracted_prime_bins K (P j) bin hbin lower N F
    (mrtTypicalCoefficient (J.erase j) P F)] at herr
  change (∫ t in -T..T, ‖D t - G t‖ ^ 2) ≤ _ at herr
  apply (mrt_restricted_energy_split D G hD hG hT.le hE).trans
  calc
    _ ≤ 2 * (1408 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1))) +
        2 * (32 * Real.exp 1 * (K.card : ℝ) *
          ∑ k ∈ K, (A k) ^ 2 * (T * lower k / (N : ℝ) + 1)) :=
      add_le_add (mul_le_mul_of_nonneg_left herr (by norm_num))
        (mul_le_mul_of_nonneg_left hg' (by norm_num))
    _ = _ := by ring

end TwoPointCorrelations

end OAI
