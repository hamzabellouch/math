import OAI.NumberTheory.CubicMoment.Estimates.LongPrimeBox
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimePredicate

namespace OAI

/-! Cancellation of the actual free selected-bin prime with the complete
two-stage stopping predicate. Only the cited Kummer prime input is used;
the stopping restriction is removed by proved bin invariance. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_stopped_selected_interval_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ w u a b : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → |u| ≤ T^H →
      ∀ (c v e : Eisenstein) (C : Finset Eisenstein), primary c → Squarefree c → v ≠ 0 →
        (¬∃ k : Eisenstein, k^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*e)) ≤ T^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool) (r : Eisenstein),
      ‖∑ p ∈ ((((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
          (fun p => largestPrimePredicate primeTieCode C p ∧ geometricPrimeBin ρ B p = j)).filter
          (fun p => stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
            j₀ k h Z Q early r (p*c)),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*cubicSymbol (p*c) v‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_prime_geometric_interval_moebius_saving hSW hA hD hH hE
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ w u a b j hT hρ hρ₂ hj hP hTP hw hu c v e C hc hs hv hnc hNv he hNe
    j₀ k h Z Q early r
  let S := (((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
    (fun p => largestPrimePredicate primeTieCode C p ∧ geometricPrimeBin ρ B p = j)
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1).1
  have hcop (p : Eisenstein) (hp : p ∈ S) : ¬p ∣ c := by
    have hpe := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hpc : IsCoprime p c := hpe.of_isCoprime_of_dvd_right (dvd_mul_right c e)
    exact fun hd => (hS p hp).2.not_isUnit (hpc.isUnit_of_dvd hd)
  have hfull : ‖∑ p ∈ S, cutoffMoebius primeDetectorCutoff w (p*c)*
      normTwist u (p*c)*cubicSymbol (p*c) v‖ ≤ K*geometricBinLower ρ B j/T^D :=
    hbound T B ρ w u a b j hT hρ hρ₂ hj hP hTP hw hu c v e C hc hs hv hnc hNv he hNe
  change ‖∑ p ∈ S with stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
    j₀ k h Z Q early r (p*c), _‖ ≤ _
  by_cases hne : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hne
    have hbin (p : Eisenstein) (hp : p ∈ S) : geometricPrimeBin ρ B p = geometricPrimeBin ρ B p₀ :=
      (Finset.mem_filter.mp hp).2.2.trans (Finset.mem_filter.mp hp₀).2.2.symm
    rw [sum_stoppedSide_same_bin S (geometricPrimeBin ρ B) (geometricBinLower ρ B)
      j₀ k h Z Q early r hc hs hp₀ hS hcop hbin]
    split_ifs
    · exact hfull
    · rw [norm_zero]
      have hP0 : 0 < geometricBinLower ρ B j := zero_lt_one.trans (hP₀.trans_le hP)
      positivity
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.filter_empty,Finset.sum_empty,norm_zero]
    have hP0 : 0 < geometricBinLower ρ B j := zero_lt_one.trans (hP₀.trans_le hP)
    positivity

end CubicFirstMoment

end

end OAI
