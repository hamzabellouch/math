import OAI.NumberTheory.TwoPointCorrelations.MRTTypicalCoarse
import OAI.NumberTheory.TwoPointCorrelations.MRTCofactorMean
import OAI.NumberTheory.TwoPointCorrelations.MRTRestrictedEnergy

namespace OAI

/-! The frequency-class energy estimate for the actual typical-set
Dirichlet polynomial. All finite bin counts and numerical coefficient
bounds are explicit; the Ramaré and endpoint error has no bin-count loss. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_typical_small_prime_energy {ι κ : Type*} [DecidableEq κ]
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P j, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower (bin p) ≤ p ∧ (p : ℝ) ≤ δ * lower (bin p))
    (hlow : ∀ k ∈ K, 1 ≤ lower k) (hupper : ∀ k ∈ K, 2 ≤ (N : ℝ) / lower k)
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    (hFb : OneBounded F) {T : ℝ} (hT : 0 < T)
    (E : Set ℝ) (hE : E ⊆ Set.Ioc (-T) T) (A : κ → ℝ)
    (hsmall : ∀ k ∈ K, ∀ t ∈ E,
      ‖mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
        (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖ ≤ A k) :
    (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖ ^ 2) ≤
      384 * Real.exp 1 * (T / (N : ℝ) + 1) *
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
  let G := mrtCoarsePolynomial (P j) (fun p => lower (bin p)) N (mrtTypicalCoefficient J P F)
  have hB : OneBounded B := mrtTypicalCoefficient_oneBounded _ _ _ hFb
  have hR (k : κ) (hk : k ∈ K) : Continuous (R k) := by
    have he : R k = mrtExponentialPolynomial
        (Ioc ⌊(N : ℝ) / lower k⌋₊ ⌊(2 * N : ℝ) / lower k⌋₊)
        (fun n => (B n / ((finitePrimeDivisorCount (P j) n + 1 : ℕ) : ℂ)) / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) :=
      funext (mrt_cofactor_exponential_polynomial (P j) B N (hlow k hk))
    rw [he]
    exact mrtExponentialPolynomial_continuous _ _ _
  have hD : Continuous D := mrtExponentialPolynomial_continuous _ _ _
  have hG : Continuous G := mrtExponentialPolynomial_continuous _ _ _
  have hsum : G = fun t => ∑ k ∈ K, Q k t * R k t :=
    funext (mrt_typical_coarse_bins J P hP hdis hj K bin hbin lower N hδ hδ2 hL F hF)
  have hg := mrt_restricted_product_sum_energy K Q R hR A hT.le hE hsmall
  have hg' : (∫ t in E, ‖G t‖ ^ 2) ≤
      32 * Real.exp 1 * (K.card : ℝ) *
        ∑ k ∈ K, (A k) ^ 2 * (T * lower k / (N : ℝ) + 1) := by
    rw [hsum]
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
  have herr := mrt_coarse_error_mean_square (P j) (hP j hj) (fun p => lower (bin p))
    hN hδ hδ2 hL (mrtTypicalCoefficient J P F)
    (mrtTypicalCoefficient_oneBounded J P F hFb) hT
  rw [mrtTypicalCoefficient_supported J P hj F] at herr
  change (∫ t in -T..T, ‖D t - G t‖ ^ 2) ≤ _ at herr
  apply (mrt_restricted_energy_split D G hD hG hT.le hE).trans
  calc
    _ ≤ 2 * (192 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1))) +
        2 * (32 * Real.exp 1 * (K.card : ℝ) *
          ∑ k ∈ K, (A k) ^ 2 * (T * lower k / (N : ℝ) + 1)) :=
      add_le_add (mul_le_mul_of_nonneg_left herr (by norm_num))
        (mul_le_mul_of_nonneg_left hg' (by norm_num))
    _ = _ := by ring

end TwoPointCorrelations

end OAI
