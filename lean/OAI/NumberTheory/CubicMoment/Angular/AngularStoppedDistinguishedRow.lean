import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularLongDistinguishedInterval
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDistinguishedRow
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDistinguishedIntervals
import OAI.NumberTheory.CubicMoment.Estimates.LongDistinguishedInterval

namespace OAI

/-! Prime cancellation with the literal distinguished-coordinate bin,
output interval and both stopping tests. The interval is derived, not
assumed to describe the stopping support. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_stopped_distinguished_prime_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u M V : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → 0 < z → 0 ≤ M → 0 ≤ V → |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → (∀ x, ‖W x‖ ≤ M) →
      (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ c d v e : Eisenstein, primary c → primary d → v ≠ 0 →
      (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 → Real.log (norm e) ≤ T^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e,
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_distinguished_mixed_interval_saving hEF ℓ hℓ hA hD hH hE hF
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w z u M V j hT hρ hρ₂ hj hP hTP hw hz hM hV hu hMV W hW hWn hWd
    c d v e hc hd hv hnc hNv he hNe j₀ k h Z Q early
  let P := geometricBinLower ρ B j
  let S := primeSurrogate (primaryPrimeFactors d) (geometricPrimeBin ρ B) (geometricBinLower ρ B)
  let E₀ := primeSurrogate (primeBinPrefix (primaryPrimeFactors d) (geometricPrimeBin ρ B) h)
    (geometricPrimeBin ρ B) (geometricBinLower ρ B)
  let lo := a/norm (c*d)
  let low := max P (Z/(norm c*S))
  let up := min (ρ*P) (min (Z*geometricBinLower ρ B j₀/(norm c*S))
    (if early = true then ρ*P else Q/(norm c*E₀)))
  let hi := b/norm (c*d)
  let C := (∀ q ∈ primaryPrimeFactors d, geometricPrimeBin ρ B q ≤ j₀) ∧
    (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ B) j₀).card = k
  let U := ((primeCutoff B).filter (fun p => IsCoprime p e)).filter
    (fun p => largestPrimePredicate primeTieCode (primaryPrimeFactors (c*d)) p)
  let f := fun p => distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v
  have heq : (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e, f p) =
      if C then ∑ p ∈ U with lo < norm p ∧ low ≤ norm p ∧ norm p < up ∧ norm p ≤ hi, f p else 0 := by
    unfold stoppedDistinguishedPrimeSet
    simp only [U,Finset.sum_filter]
    by_cases hC : C
    · rw [ite_eq_left hC]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hcop : IsCoprime p e
      · by_cases hl : largestPrimePredicate primeTieCode (primaryPrimeFactors (c*d)) p
        · simp only [hcop,hl,ite_true]
          have hinterval := stopped_distinguished_interval_iff (a := a) (b := b) (j₀ := j₀) (k := k) (h := h) hρ hρ₂ hj Z Q early hc hd
            (mem_primeCutoff.mp hp).1 (mem_primeCutoff.mp hp).2
          have hi' : (geometricPrimeBin ρ B p = j ∧
              (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
              stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
                j₀ k h Z Q early (c*p) d) ↔
              lo < norm p ∧ low ≤ norm p ∧ norm p < up ∧ norm p ≤ hi := by
            constructor
            · intro hpred
              exact (hinterval.mp hpred).2
            · intro hq
              exact hinterval.mpr ⟨hC,hq⟩
          exact if_congr hi' rfl rfl
        · simp only [hcop,hl,ite_true,ite_false]
      · simp only [hcop,ite_false]
    · rw [ite_eq_right hC]
      apply Finset.sum_eq_zero
      intro p hp
      by_cases hcop : IsCoprime p e
      · by_cases hl : largestPrimePredicate primeTieCode (primaryPrimeFactors (c*d)) p
        · simp only [hcop,hl,ite_true]
          apply ite_eq_right
          intro hpred
          have hinterval := stopped_distinguished_interval_iff (a := a) (b := b) (j₀ := j₀) (k := k) (h := h) hρ hρ₂ hj Z Q early hc hd
            (mem_primeCutoff.mp hp).1 (mem_primeCutoff.mp hp).2
          exact hC (hinterval.mp hpred).1
        · simp only [hcop,hl,ite_true,ite_false]
      · simp only [hcop,ite_false]
  have hPpos : 0 < P := zero_lt_one.trans (geometricBinLower_gt_one hρ hj)
  change ‖∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e, f p‖ ≤ _
  rw [heq]
  by_cases hC : C
  · rw [ite_eq_left hC]
    exact hbound T P B lo low up hi w z u M V hT hP hTP
      ((le_max_left _ _).trans (le_max_right _ _))
      ((min_le_left _ _).trans ((min_le_left _ _).trans
        (mul_le_mul_of_nonneg_right hρ₂ hPpos.le)))
      hw hz hM hV hu hMV W hW hWn hWd v e (primaryPrimeFactors (c*d)) hv hnc hNv he hNe
  · rw [ite_eq_right hC,norm_zero]
    positivity

end CubicFirstMoment

end

end OAI
