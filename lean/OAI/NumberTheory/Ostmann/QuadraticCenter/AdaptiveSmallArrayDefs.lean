import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveSmallArrayEnvelope

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def adaptiveSmallBaseParameters (L Z : ℕ) : Finset AdaptiveArrayParameters := by
  classical
  exact (adaptiveArrayParameters L Z).filter (fun a => a.multiple=1 ∧ (L^6:ℕ) ≤ a.radius)

def adaptiveOffEventParameters (L Z : ℕ) (A : ∀ p : ℕ, Finset (ZMod p))
    (K : ℝ) : Finset AdaptiveArrayParameters := by
  classical
  exact (adaptiveSmallBaseParameters L Z).filter (fun a =>
    ∀ s ∈ adaptiveSmallSupport L, ∀ d ∈ L.divisors, ∀ v ∈ L.divisors,
      ‖divisorQuadraticSumP d A (adaptiveInverse a.modulusResidue d) s v 1
        a.radius a.phaseResidue a.theta‖ ≤
        Real.sqrt ((2:ℝ)^d.primeFactors.card)*Real.exp (-(9/10:ℝ)*K))

def adaptiveNoSmallWitness (L M : ℕ) (A : ∀ p : ℕ, Finset (ZMod p))
    (R : ℝ) (h : ℤ) (θ K : ℝ) : Prop :=
  ∀ s ∈ adaptiveSmallSupport L, ∀ d ∈ L.divisors, ∀ v ∈ L.divisors,
    ‖divisorQuadraticSumP d A (adaptiveInverse M d) s v 1 R h θ‖ ≤
      Real.sqrt ((2:ℝ)^d.primeFactors.card)*Real.exp (-K)

def adaptiveSmallArray (L : ℕ) (lam : ℝ) (A : ∀ p : ℕ, Finset (ZMod p))
    (a : AdaptiveArrayParameters) (s : ℕ) : ℂ := by
  classical
  exact if s ∈ adaptiveSmallSupport L then
    positiveDivisorArray L a.modulusResidue lam A (adaptiveInverse a.modulusResidue)
      1 a.radius a.phaseResidue a.theta s else 0

def adaptiveOffEventArrayFamily (L Z : ℕ) (lam : ℝ)
    (A : ∀ p : ℕ, Finset (ZMod p)) (K : ℝ) : Finset (ℕ → ℂ) := by
  classical
  exact (adaptiveOffEventParameters L Z A K).image (adaptiveSmallArray L lam A)

def adaptiveSmallArrayFamily (L Z : ℕ) (lam : ℝ)
    (A : ∀ p : ℕ, Finset (ZMod p)) : Finset (ℕ → ℂ) := by
  classical
  exact (adaptiveSmallBaseParameters L Z).image (adaptiveSmallArray L lam A)

theorem adaptiveSmallSupport_subset {L Z : ℕ} (hZ : 1 ≤ Z) (hLZ : L ≤ Z) :
    adaptiveSmallSupport L ⊆ adaptiveArraySupport L Z := by
  intro s hs
  obtain ⟨hsI,hsf,hcop⟩ := Finset.mem_filter.mp hs
  obtain ⟨hslo,hshi⟩ := Finset.mem_Ico.mp hsI
  have hpow : L^4 ≤ Z^14 := (Nat.pow_le_pow_left hLZ 4).trans
    (Nat.pow_le_pow_right hZ (by omega))
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hslo,by omega⟩,hsf,hcop⟩

theorem divisorQuadraticSumP_canonical_reduction {L d M : ℕ} (hL : Squarefree L)
    (hd : d ∈ L.divisors) (A : ∀ p : ℕ, Finset (ZMod p))
    (s v P : ℕ) (R θ : ℝ) (h : ℤ) :
    divisorQuadraticSumP d A (adaptiveInverse M d) s v P R h θ =
      divisorQuadraticSumP d A (adaptiveInverse (M%(4*L)) d) s v P R
        (adaptivePhaseResidue L h) θ := by
  have hdsq := hL.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  have hInv : (adaptiveInverse M d:ZMod d)=(adaptiveInverse (M%(4*L)) d:ZMod d) := by
    rw [adaptiveInverse_cast,adaptiveInverse_cast,adaptive_mod_cast (Nat.dvd_of_mem_divisors hd)]
  rw [divisorQuadraticSumP_inverse_congr hdsq A hInv]
  have hphase : (d:ℤ) ∣ h-(adaptivePhaseResidue L h:ℕ) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ d).mp
    simpa only [Int.cast_natCast] using
      adaptivePhaseResidue_cast hL.ne_zero.bot_lt (Nat.dvd_of_mem_divisors hd) h
  exact divisorQuadraticSumP_phase_congr hdsq A _ s v P R θ hphase

end Ostmann.QuadraticCenter

end

end OAI
