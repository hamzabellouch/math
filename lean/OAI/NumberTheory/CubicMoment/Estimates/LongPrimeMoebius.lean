import OAI.NumberTheory.CubicMoment.Estimates.PrimeMoebiusExtraction
import OAI.NumberTheory.CubicMoment.Estimates.LongPrimeCutoff

namespace OAI

/-! The free selected-bin prime in the literal cutoff-Mobius coefficient.
All other factors remain fixed, including the coprimality exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_prime_moebius_bound (hSW : KummerPrimeSiegelWalfisz)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w →
      ∀ c v e : Eisenstein, primary c → Squarefree c → v ≠ 0 →
        (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p (c*e)),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*cubicSymbol (p*c) v‖ ≤
        K*P/T^D*(1+|u|)+Real.log (norm (c*e))/Real.log 2 := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_prime_cutoff_excluded_bound hSW hA hD
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T P a b w u hT hP hTP ha hab hb hw c v e hc hs hv hnc hNv he
  let S := ((primeCutoff b).filter (fun p => a < norm p)).filter
    (fun p => IsCoprime p (c*e))
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hfilter : S.filter (fun p => ¬p ∣ c) = S := by
    apply Finset.filter_true_of_mem
    intro p hp hd
    have hpe := (Finset.mem_filter.mp hp).2
    have hpc : IsCoprime p c := hpe.of_isCoprime_of_dvd_right (dvd_mul_right c e)
    exact (hS p hp).2.not_isUnit (hpc.isUnit_of_dvd hd)
  have hid := cutoffMoebius_free_prime_identity S hS primeDetectorCutoff w u hc hs v
  rw [hfilter] at hid
  have hpref := cutoffMoebius_free_prime_prefactor_bound
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) w u hc v
  change ‖∑ p ∈ S, _‖ ≤ _
  rw [hid,norm_mul]
  apply (mul_le_of_le_one_left (_root_.norm_nonneg _) hpref).trans
  simpa only [normTwist_eq_mellinPhase] using
    hbound T P a b w u hT hP hTP ha hab hb hw v (c*e) hv hnc hNv
      (mul_ne_zero (primary_ne_zero hc) he)

end CubicFirstMoment

end

end OAI
