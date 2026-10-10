import OAI.NumberTheory.TwoPointCorrelations.MRTGeneralFactorization
import OAI.NumberTheory.TwoPointCorrelations.MRTRestrictedEnergy

namespace OAI

/-! The actual typical-set Ramaré approximation for ordinary
multiplicative functions. Prime squares account for every failure of
complete multiplicativity, before any frequency-class witness cover. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrtCofactorPolynomial_continuous (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) (a : ℝ) : Continuous (mrtCofactorPolynomial P F N a) := by
  unfold mrtCofactorPolynomial
  apply continuous_finsetSum
  intro m _
  by_cases hw : (N : ℝ) < a * m ∧ a * m ≤ 2 * N
  · simp only [ite_eq_left hw]
    unfold mrtDirichletAtom
    fun_prop
  · simp only [ite_eq_right hw]
    exact continuous_const

lemma mrt_extracted_prime_bins {κ : Type*} [DecidableEq κ]
    (K : Finset κ) (P : Finset ℕ) (bin : ℕ → κ)
    (hbin : ∀ p ∈ P, bin p ∈ K) (lower : κ → ℝ) (N : ℕ)
    (A B : ℕ → ℂ) (t : ℝ) :
    (∑ p ∈ P, mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (lower (bin p)) t) =
      ∑ k ∈ K,
        mrtExponentialPolynomial (P.filter (fun p => bin p = k))
          (fun p => A p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t *
        mrtCofactorPolynomial P B N (lower k) t := by
  rw [← sum_fiberwise_of_maps_to hbin]
  apply sum_congr rfl
  intro k _
  unfold mrtExponentialPolynomial
  rw [sum_mul]
  apply sum_congr rfl
  intro p hp
  have hbp := (mem_filter.mp hp).2
  simp only [mrtDirichletAtom, hbp]

theorem mrt_typical_general_prime_mean_square {ι : Type*}
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (lower : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower p ≤ p ∧ (p : ℝ) ≤ δ * lower p)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t -
        ∑ p ∈ P j, mrtDirichletAtom F p t *
          mrtCofactorPolynomial (P j) (mrtTypicalCoefficient (J.erase j) P F) N (lower p) t‖ ^ 2) ≤
      1408 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) := by
  let C := mrtTypicalCoefficient J P F
  let B := mrtTypicalCoefficient (J.erase j) P F
  let D := mrtDyadicPolynomial C N
  let G := mrtCoarsePolynomial (P j) lower N C
  let H : ℝ → ℂ := fun t => ∑ p ∈ P j, mrtDirichletAtom F p t *
    mrtCofactorPolynomial (P j) B N (lower p) t
  have hD : Continuous D := mrtExponentialPolynomial_continuous _ _ _
  have hG : Continuous G := mrtExponentialPolynomial_continuous _ _ _
  have hR (p : ℕ) : Continuous (fun t => mrtCofactorPolynomial (P j) B N (lower p) t) :=
    mrtCofactorPolynomial_continuous (P j) B N (lower p)
  have hH : Continuous H := by
    apply continuous_finsetSum
    intro p _
    apply Continuous.mul _ (hR p)
    unfold mrtDirichletAtom
    fun_prop
  have hboundary := mrt_coarse_error_mean_square (P j) (hP j hj) lower
    hN hδ hδ2 hL C (mrtTypicalCoefficient_oneBounded J P F hFb) hT
  rw [mrtTypicalCoefficient_supported J P hj F] at hboundary
  change (∫ t in -T..T, ‖D t - G t‖ ^ 2) ≤ _ at hboundary
  have hproduct := mrt_general_prime_factorization_mean (P j) (hP j hj) lower hN hδ hδ2 hL
    C F B (mrtTypicalCoefficient_oneBounded J P F hFb) hFb
    (mrtTypicalCoefficient_oneBounded (J.erase j) P F hFb)
    (fun p hp m hm hpm => mrtTypicalCoefficient_prime_mul_coprime J P hP hdis hj F hF hp hm hpm)
    hT
  change (∫ t in -T..T, ‖G t - H t‖ ^ 2) ≤ _ at hproduct
  have hproduct' : (∫ t in -T..T, ‖G t - H t‖ ^ 2) ≤
      512 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) := by
    apply hproduct.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_right (by linarith)
  have hs := mrt_restricted_energy_split (fun t => D t - H t) (fun t => G t - H t)
    (hD.sub hH) (hG.sub hH) hT.le (Set.Subset.refl (Set.Ioc (-T) T))
  have he (t : ℝ) : (D t - H t) - (G t - H t) = D t - G t := by ring
  simp only [he, ← intervalIntegral.integral_of_le (show -T ≤ T by linarith)] at hs
  apply hs.trans
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hboundary (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hproduct' (by norm_num : (0 : ℝ) ≤ 2))
  convert hh using 1; ring

end TwoPointCorrelations

end OAI
