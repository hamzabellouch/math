import OAI.NumberTheory.TwoPointCorrelations.MRTCoarseFactorization
import OAI.NumberTheory.TwoPointCorrelations.MRTTypicalRamare

namespace OAI

/-! Coarse Ramaré factorization on the actual typical-factorization set.
Removing a prime from the selected band leaves precisely the other-band
mask; the square and endpoint errors retain their uniform finite bounds. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtTypicalCoefficient {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (n : ℕ) : ℂ :=
  if mrtTypical J P n then F n else 0

lemma mrtTypicalCoefficient_oneBounded {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F) :
    OneBounded (mrtTypicalCoefficient J P F) := by
  intro n hn
  unfold mrtTypicalCoefficient
  split_ifs
  · exact hF n hn
  · simp

lemma mrtTypicalCoefficient_supported {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) {j : ι} (hj : j ∈ J) (F : ℕ → ℂ) :
    mrtSupportedCoefficient (P j) (mrtTypicalCoefficient J P F) =
      mrtTypicalCoefficient J P F := by
  funext n
  exact mrtTypical_ramare_supported J P hj F n

lemma mrtTypicalCoefficient_prime_mul {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    {p : ℕ} (hp : p ∈ P j) {m : ℕ} (hm : 0 < m) :
    mrtTypicalCoefficient J P F (p * m) =
      F p * mrtTypicalCoefficient (J.erase j) P F m := by
  unfold mrtTypicalCoefficient
  rw [mrtTypical_prime_mul J P hP hdis hj hp]
  split_ifs
  · exact hF p m (hP j hj p hp).pos hm
  · simp

/-- The factorization on a fixed typical band produces the literal
short prime polynomial and the other-band cofactor polynomial. -/
theorem mrt_typical_coarse_bins {ι κ : Type*} [DecidableEq κ]
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P j, bin p ∈ K)
    (lower : κ → ℝ) (N : ℕ) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower (bin p) ≤ p ∧ (p : ℝ) ≤ δ * lower (bin p))
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b) (t : ℝ) :
    mrtCoarsePolynomial (P j) (fun p => lower (bin p)) N
      (mrtTypicalCoefficient J P F) t =
      ∑ k ∈ K,
        mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
          (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t *
        mrtCofactorPolynomial (P j) (mrtTypicalCoefficient (J.erase j) P F)
          N (lower k) t := by
  apply mrt_coarse_polynomial_bins_of_product K (P j) (hP j hj) bin hbin lower N
    hδ hδ2 hL
  intro p hp m hm
  exact mrtTypicalCoefficient_prime_mul J P hP hdis hj F hF hp hm

/-- The binned factorization approximates the actual typical polynomial
in mean square, with no bin-count loss in the error. -/
theorem mrt_typical_coarse_mean_square {ι κ : Type*} [DecidableEq κ]
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P j, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower (bin p) ≤ p ∧ (p : ℝ) ≤ δ * lower (bin p))
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    (hFb : OneBounded F) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t -
      ∑ k ∈ K,
        mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
          (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t *
        mrtCofactorPolynomial (P j) (mrtTypicalCoefficient (J.erase j) P F)
          N (lower k) t‖ ^ 2) ≤
      192 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) := by
  have hb := mrt_coarse_error_mean_square (P j) (hP j hj) (fun p => lower (bin p))
    hN hδ hδ2 hL (mrtTypicalCoefficient J P F)
    (mrtTypicalCoefficient_oneBounded J P F hFb) hT
  rw [mrtTypicalCoefficient_supported J P hj F] at hb
  simpa only [mrt_typical_coarse_bins J P hP hdis hj K bin hbin lower N
    hδ hδ2 hL F hF] using hb

end TwoPointCorrelations

end OAI
