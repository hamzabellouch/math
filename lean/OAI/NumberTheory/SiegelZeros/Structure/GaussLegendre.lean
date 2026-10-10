import Mathlib.NumberTheory.GaussSum
import OAI.NumberTheory.SiegelZeros.Determinants.ThetaDivisibility

namespace OAI

namespace SiegelZeros


namespace Awei.W39

theorem intCast_ne_zero_of_not_dvd_natAbs {R : Type*} [Ring R]
    (p : ℕ) [CharP R p] (D : ℤ) (hD : ¬ p ∣ D.natAbs) : (D : R) ≠ 0 := by
  rw [ne_eq, CharP.intCast_eq_zero_iff R p, Int.natCast_dvd]
  exact hD

variable {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]

theorem frobenius_eigenvalue_eq_legendre (hp : p ≠ 2) (a : F) (D c : ℤ)
    (ha : a ^ 2 = (D : F)) (hD : (D : F) ≠ 0)
    (hc : c = 0 ∨ c = 1 ∨ c = -1) (hf : a ^ p = (c : F) * a) :
    c = legendreSym p D := by
  have ha0 : a ≠ 0 := by
    intro hz
    apply hD
    rw [← ha, hz, zero_pow (by decide : 2 ≠ 0)]
  have he : (c : F) = (legendreSym p D : F) :=
    mul_right_cancel₀ ha0 (hf.symm.trans (root_pow_prime p hp a D ha))
  have hDZ : (D : ZMod p) ≠ 0 := by
    intro hz
    apply hD
    have hm := congrArg (ZMod.castHom (dvd_refl p) F) hz
    simpa only [map_intCast, map_zero] using hm
  have hleg : legendreSym p D = 0 ∨ legendreSym p D = 1 ∨
      legendreSym p D = -1 := Or.inr (legendreSym.eq_one_or_neg_one p hDZ)
  have hchar : ringChar F ≠ 2 := by
    simpa only [ringChar.eq F p] using hp
  apply Int.cast_injOn_of_ringChar_ne_two hchar
  · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hc
  · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hleg
  · exact he

theorem integerCharacter_legendre_of_gaussSum_sq
    {S : Type*} [CommRing S] [Fintype S]
    (hp : p ≠ 2) (χ : MulChar S ℤ) (hq : χ.IsQuadratic)
    (hu : IsUnit (p : S)) (ψ : AddChar S F) (D : ℤ)
    (hD : (D : F) ≠ 0)
    (hs : gaussSum (χ.ringHomComp (Int.castRingHom F)) ψ ^ 2 = (D : F)) :
    χ (p : S) = legendreSym p D := by
  apply frobenius_eigenvalue_eq_legendre p hp _ D _ hs hD (hq (p : S))
  exact (hq.comp (Int.castRingHom F)).gaussSum_frob p hu ψ

end Awei.W39


end SiegelZeros

end OAI
