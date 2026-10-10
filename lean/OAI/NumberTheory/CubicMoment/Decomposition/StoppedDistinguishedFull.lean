import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDistinguishedRow

namespace OAI

/-! Restoring the fixed complementary cubic character and the original
Möbius coefficient in the distinguished-coordinate prime sum. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedDistinguishedPrimeSet_primary (B ρ a b : ℝ) (j j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (c d e : Eisenstein) {p : Eisenstein}
    (hp : p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e) :
    primaryPrime p :=
  (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
    (Finset.mem_filter.mp hp).1).1).1).1

lemma distinguished_full_prime_norm (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (W : ℝ → ℂ) (w z u : ℝ)
    (c d v : Eisenstein) (hc : primary c) (hd : primary d) :
    ‖∑ p ∈ S, cutoffMoebius primeDetectorCutoff w d*
      distinguishedRadialWeight W w z (norm p)*normTwist u ((c*p)*d)*
        cubicSymbol ((c*p)*d) v‖ ≤
      ‖∑ p ∈ S, distinguishedRadialWeight W w z (norm p)*
        mellinPhase u (norm p)*cubicSymbol p v‖ := by
  have hsplit : (∑ p ∈ S, cutoffMoebius primeDetectorCutoff w d*
      distinguishedRadialWeight W w z (norm p)*normTwist u ((c*p)*d)*
        cubicSymbol ((c*p)*d) v) =
      cutoffMoebius primeDetectorCutoff w d*
        ∑ p ∈ S, distinguishedRadialWeight W w z (norm p)*normTwist u ((c*d)*(p*1))*
          cubicSymbol ((c*d)*(p*1)) v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have he : (c*p)*d = (c*d)*(p*1) := by ring
    rw [he]
    ring
  rw [hsplit,norm_mul]
  calc
    _ ≤ ‖∑ p ∈ S, distinguishedRadialWeight W w z (norm p)*normTwist u ((c*d)*(p*1))*
          cubicSymbol ((c*d)*(p*1)) v‖ :=
      mul_le_of_le_one_left (_root_.norm_nonneg _) (primeDetectorCutoff_moebius_norm w d)
    _ ≤ ‖∑ p ∈ S, distinguishedRadialWeight W w z (norm p)*normTwist u (p*1)*
          cubicSymbol (p*1) v‖ :=
      fixed_primary_free_prime_norm S hS (fun p => distinguishedRadialWeight W w z (norm p))
        (c*d) 1 v (primary_mul hc hd) primary_one u
    _ = _ := by simp only [mul_one,normTwist_eq_mellinPhase]

theorem stopped_distinguished_full_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u M V : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → 0 < z → 0 ≤ M → 0 ≤ V → |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → (∀ x, ‖W x‖ ≤ M) →
      (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ c d v e : Eisenstein, primary c → primary d → v ≠ 0 →
      (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      Real.log (norm (c*(d*e))) ≤ T^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e)),
        cutoffMoebius primeDetectorCutoff w d*distinguishedRadialWeight W w z (norm p)*
          normTwist u ((c*p)*d)*cubicSymbol ((c*p)*d) v‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := stopped_distinguished_prime_saving hSW hA hD hH hE hF
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w z u M V j hT hρ hρ₂ hj hP hTP hw hz hM hV hu hMV W hW hWn hWd
    c d v e hc hd hv hnc hNv he hNe j₀ k h Z Q early
  apply (distinguished_full_prime_norm
    (stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e)))
    (fun p hp => stoppedDistinguishedPrimeSet_primary B ρ a b j j₀ k h Z Q early c d (c*(d*e)) hp)
    W w z u c d v hc hd).trans
  exact hbound T B ρ a b w z u M V j hT hρ hρ₂ hj hP hTP hw hz hM hV hu hMV W hW hWn hWd
    c d v (c*(d*e)) hc hd hv hnc hNv
    (mul_ne_zero (primary_ne_zero hc) (mul_ne_zero (primary_ne_zero hd) he)) hNe
    j₀ k h Z Q early

end CubicFirstMoment

end

end OAI
