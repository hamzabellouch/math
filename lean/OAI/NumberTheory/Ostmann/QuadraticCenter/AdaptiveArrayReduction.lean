import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArrayResidues

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem positiveDivisorArray_residue_reduction {L M : ℕ} (hL : Squarefree L)
    (hM : Odd M) (lam : ℝ) (A : ∀ p : ℕ, Finset (ZMod p))
    (mInv : ℕ → ℤ)
    (hmInv : ∀ d ∈ L.divisors, (mInv d : ZMod d) = (M:ZMod d)⁻¹)
    (P : ℕ) (R θ : ℝ) (h : ℤ) (s : ℕ) :
    positiveDivisorArray L M lam A mInv P R h θ s =
      positiveDivisorArray L (M%(4*L)) lam A (adaptiveInverse (M%(4*L))) P R
        (adaptivePhaseResidue L h) θ s := by
  unfold positiveDivisorArray
  apply congrArg (fun term : ℂ => (Real.sqrt (s : ℝ) : ℂ)⁻¹ * term)
  apply Finset.sum_congr rfl
  intro v hv
  rw [adaptive_jacobi_mod (Nat.dvd_of_mem_divisors hv) hM]
  apply congrArg (fun term : ℂ =>
    (jacobiSym (v : ℤ) (M%(4*L)) : ℂ) / (Real.sqrt (v : ℝ) : ℂ) * term)
  apply Finset.sum_congr rfl
  intro d hd
  rw [adaptive_jacobi_mod (Nat.dvd_of_mem_divisors hd) hM]
  apply congrArg (fun term : ℂ =>
    (lam : ℂ)^d.primeFactors.card * (jacobiSym (d : ℤ) (M%(4*L)) : ℂ) * term)
  have hdsq := hL.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  have hInv : (mInv d:ZMod d) = (adaptiveInverse (M%(4*L)) d:ZMod d) := by
    rw [hmInv d hd,adaptiveInverse_cast,adaptive_mod_cast (Nat.dvd_of_mem_divisors hd)]
  have hphase : (d:ℤ) ∣ h-(adaptivePhaseResidue L h:ℕ) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ d).mp
    simpa only [Int.cast_natCast] using
      adaptivePhaseResidue_cast hL.ne_zero.bot_lt (Nat.dvd_of_mem_divisors hd) h
  refine (divisorQuadraticSumP_inverse_congr hdsq A hInv s v P R h θ).trans ?_
  simpa only [Int.cast_natCast] using
    divisorQuadraticSumP_phase_congr hdsq A _ s v P R θ hphase

theorem positiveDivisorArray_canonical_reduction {L M : ℕ} (hL : Squarefree L)
    (hM : Odd M) (lam : ℝ) (A : ∀ p : ℕ, Finset (ZMod p))
    (P : ℕ) (R θ : ℝ) (h : ℤ) (s : ℕ) :
    positiveDivisorArray L M lam A (adaptiveInverse M) P R h θ s =
      positiveDivisorArray L (M%(4*L)) lam A (adaptiveInverse (M%(4*L))) P R
        (adaptivePhaseResidue L h) θ s :=
  positiveDivisorArray_residue_reduction hL hM lam A (adaptiveInverse M)
    (fun d _ => adaptiveInverse_cast M d) P R θ h s

end Ostmann.QuadraticCenter

end

end OAI
