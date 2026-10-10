import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimeFactorization

namespace OAI

/-! The selected-bin free-prime row with its actual full product,
complementary exclusion and both stopping tests. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedSelectedPrimeSet (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r c e : Eisenstein) : Finset Eisenstein :=
  ((((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter
    (fun p => IsCoprime p (c*(r*e)))).filter
    (fun p => largestPrimePredicate primeTieCode (primaryPrimeFactors (r*c)) p ∧
      geometricPrimeBin ρ B p = j)).filter
    (fun p => stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
      j₀ k h Z Q early r (p*c))

def stoppedSelectedPrimeRow (B ρ a b w u : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r c v e : Eisenstein) : ℂ :=
  ∑ p ∈ stoppedSelectedPrimeSet B ρ a b j j₀ k h Z Q early r c e,
    cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (r*(p*c))*cubicSymbol (r*(p*c)) v

lemma stoppedSelectedPrimeSet_primary (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r c e : Eisenstein) {p : Eisenstein}
    (hp : p ∈ stoppedSelectedPrimeSet B ρ a b j j₀ k h Z Q early r c e) : primaryPrime p := by
  exact (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1).1).1

theorem stopped_selected_prime_row_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w u : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → |u| ≤ T^H →
      ∀ r c v e : Eisenstein, primary r → primary c → Squarefree c → v ≠ 0 →
        (¬∃ k : Eisenstein, k^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*(r*e))) ≤ T^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖stoppedSelectedPrimeRow B ρ a b w u j j₀ k h Z Q early r c v e‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_stopped_selected_interval_saving hSW hA hD hH hE
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w u j hT hρ hρ₂ hj hP hTP hw hu r c v e hr hc hs hv hnc hNv he hNe
    j₀ k h Z Q early
  unfold stoppedSelectedPrimeRow
  apply (fixed_primary_free_prime_norm (stoppedSelectedPrimeSet B ρ a b j j₀ k h Z Q early r c e)
    (fun p hp => stoppedSelectedPrimeSet_primary B ρ a b j j₀ k h Z Q early r c e hp)
    (fun p => cutoffMoebius primeDetectorCutoff w (p*c)) r c v hr hc u).trans
  exact hbound T B ρ w u a b j hT hρ hρ₂ hj hP hTP hw hu c v (r*e)
    (primaryPrimeFactors (r*c)) hc hs hv hnc hNv (mul_ne_zero (primary_ne_zero hr) he) hNe
    j₀ k h Z Q early r

end CubicFirstMoment

end

end OAI
