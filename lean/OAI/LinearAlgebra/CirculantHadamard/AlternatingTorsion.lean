import OAI.LinearAlgebra.CirculantHadamard.AlternatingField
import OAI.LinearAlgebra.CirculantHadamard.AlternatingLocalization
import OAI.LinearAlgebra.CirculantHadamard.CyclotomicTorsion
import OAI.LinearAlgebra.CirculantHadamard.PrimeCharacterEvaluations
import OAI.LinearAlgebra.CirculantHadamard.ResidueTorsion

namespace OAI

/-!
# The actual alternating character product has odd torsion

The index is the full set of prime divisors of u. The local comparison and
all-maximal-ideal argument are applied to the actual partial evaluations of
the given constant-norm group-ring element. No edge-comparison, integrality,
complex-norm, or torsion conclusion is assumed.
-/

noncomputable section

namespace CirculantHadamard

open CyclotomicRings PrimeComponents PrimeCharacterEvaluations
open AlternatingLocalization

/-- The single fixed field element used for every prime-direction comparison. -/
abbrev alternatingValue (u : ℕ) (hu : 0 < u)
    (x : CyclicRing.Elem GaussianRing (u ^ 2)) : FractionRing (B u) :=
  alternatingProduct (Finset.univ : Finset (PrimeIndex u))
    (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S x))

/-- Denominator removal and all complex homomorphisms are discharged for the
actual character values before invoking Kronecker's criterion. -/
theorem exists_integral_alternating_root_of_unity (u : ℕ) [NeZero (u ^ 2)]
    (hu : 1 < u) (huodd : Odd u) (x : CyclicRing.Elem GaussianRing (u ^ 2))
    (hx : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    ∃ z : B u,
      algebraMap (B u) (FractionRing (B u)) z =
        alternatingValue u (lt_trans Nat.zero_lt_one hu) x ∧
      ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  classical
  let hu0 : 0 < u := lt_trans Nat.zero_lt_one hu
  obtain ⟨z, hz⟩ := exists_integral_alternatingProduct u hu0 huodd x hx
  refine ⟨z, hz, B_root_of_unity u z ?_⟩
  intro σ
  have ht : (Finset.univ : Finset (PrimeIndex u)).Nonempty := by
    obtain ⟨p, hp⟩ := primes_nonempty hu
    exact ⟨⟨p, hp⟩, Finset.mem_univ _⟩
  have hne : ∀ S ⊆ (Finset.univ : Finset (PrimeIndex u)),
      algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu0 S x) ≠ 0 := by
    intro S _ hS
    apply subsetEvaluation_ne_zero u hu0 S x hx
    apply IsFractionRing.injective (B u) (FractionRing (B u))
    simpa only [map_zero] using hS
  exact norm_hom_integral_alternatingProduct
    (algebraMap (B u) (FractionRing (B u)))
    (IsFractionRing.injective (B u) (FractionRing (B u)))
    Finset.univ ht (fun S => subsetEvaluation u hu0 S x) z hne hz σ (u : ℝ)
    (by exact_mod_cast hu0) (fun S _ => subsetEvaluation_map_norm u hu0 S x hx σ)

/-- The same alternating product is killed by a power of every actual prime
dividing u. The maximal ideal and characteristic-p residue field are built
from the concrete integral coefficient ring. -/
theorem alternatingProduct_prime_power_torsion (u : ℕ) [NeZero (u ^ 2)]
    (hu : 1 < u) (huodd : Odd u) (x : CyclicRing.Elem GaussianRing (u ^ 2))
    (hx : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p : PrimeIndex u) :
    ∃ a : ℕ, (alternatingValue u (lt_trans Nat.zero_lt_one hu) x) ^ (p.val ^ a) = 1 := by
  classical
  let hu0 : 0 < u := lt_trans Nat.zero_lt_one hu
  obtain ⟨z, hz, hfinite⟩ := exists_integral_alternating_root_of_unity u hu huodd x hx
  have hp : p.val.Prime := prime_of_mem p.property
  obtain ⟨m, hm, _, hpm⟩ := exists_maximal_ideal_over_nat_prime_of_charZero (B u) hp
  let M : MaximalSpectrum (B u) := ⟨m, hm⟩
  let : Algebra (B u) (AtMaximal (B u) M) := B_local_algebra u M
  obtain ⟨v, hv, hvres⟩ :=
    exists_local_unit_alternatingProduct u hu0 huodd x hx p M hpm
  have hlocal : algebraMap (B u) (AtMaximal (B u) M) z =
      (v : AtMaximal (B u) M) :=
    local_representative_eq (FractionRing (B u)) M z v (hz.trans hv.symm)
  let : CharP (IsLocalRing.ResidueField (AtMaximal (B u) M)) p.val :=
    residue_charP M p.val hp hpm
  let f : B u →+* IsLocalRing.ResidueField (AtMaximal (B u) M) :=
    (IsLocalRing.residue (AtMaximal (B u) M)).comp
      (algebraMap (B u) (AtMaximal (B u) M))
  have hres : f z = 1 := by
    change IsLocalRing.residue (AtMaximal (B u) M)
      (algebraMap (B u) (AtMaximal (B u) M) z) = 1
    rw [hlocal]
    exact hvres
  obtain ⟨a, ha⟩ := exists_prime_power_of_residue_one f z hp hres hfinite
  refine ⟨a, ?_⟩
  have h := congrArg (algebraMap (B u) (FractionRing (B u))) ha
  simpa only [map_pow, map_one, hz] using h

/-- The actual subset-character product has a positive odd torsion exponent. -/
theorem alternatingProduct_odd_torsion (u : ℕ) [NeZero (u ^ 2)]
    (hu : 1 < u) (huodd : Odd u) (x : CyclicRing.Elem GaussianRing (u ^ 2))
    (hx : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u : GaussianRing) ^ 2)) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingValue u (lt_trans Nat.zero_lt_one hu) x) ^ m = 1 := by
  classical
  have hx' : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing) := by
    simpa only [Nat.cast_pow] using hx
  obtain ⟨p, hp⟩ := primes_nonempty hu
  obtain ⟨a, ha⟩ := alternatingProduct_prime_power_torsion u hu huodd x hx' ⟨p, hp⟩
  exact ⟨p ^ a, pow_pos (prime_of_mem hp).pos _, (odd_of_mem huodd hp).pow, ha⟩

/-- With two distinct prime directions the single fixed product is one. -/
theorem alternatingProduct_eq_one_of_two_primes (u : ℕ) [NeZero (u ^ 2)]
    (hu : 1 < u) (huodd : Odd u) (x : CyclicRing.Elem GaussianRing (u ^ 2))
    (hx : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p q : PrimeIndex u) (hpq : p ≠ q) :
    alternatingValue u (lt_trans Nat.zero_lt_one hu) x = 1 := by
  obtain ⟨a, ha⟩ := alternatingProduct_prime_power_torsion u hu huodd x hx p
  obtain ⟨b, hb⟩ := alternatingProduct_prime_power_torsion u hu huodd x hx q
  have hcop : Nat.Coprime (p.val ^ a) (q.val ^ b) :=
    Nat.coprime_pow_primes a b (prime_of_mem p.property) (prime_of_mem q.property)
      (fun h => hpq (Subtype.ext h))
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one hb)
  have hd1 : orderOf (alternatingValue u (lt_trans Nat.zero_lt_one hu) x) ∣ 1 := by
    simpa only [hcop.gcd_eq_one] using hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)

end CirculantHadamard

end

end OAI
