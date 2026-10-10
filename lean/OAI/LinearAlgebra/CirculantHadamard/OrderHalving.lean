import OAI.LinearAlgebra.CirculantHadamard.CyclicRing
import OAI.LinearAlgebra.CirculantHadamard.ProjectionCoefficients
import OAI.LinearAlgebra.CirculantHadamard.OrderCyclotomicDivisibility
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Halving an odd-coefficient dyadic group-ring element

The integer averaging lemmas retain the original paired coefficients.
The group-ring step uses their actual quotient fiber sums and the concrete
cyclotomic divisibility theorem; the ring is not assumed to be a domain.
-/

namespace CirculantHadamard

open CyclicRing

/-- The coefficient obtained by projecting a pair and dividing by two. -/
def pairAverage (a b : ℤ) : ℤ := (a + b) / 2

theorem two_mul_pairAverage {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    2 * pairAverage a b = a + b := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨s, hs⟩ := hb
  dsimp [pairAverage]
  omega

/-- Congruent odd coefficients modulo four have an odd integral average. -/
theorem odd_pairAverage {a b : ℤ} (hb : Odd b) (hab : (4 : ℤ) ∣ a - b) :
    Odd (pairAverage a b) := by
  obtain ⟨r, hr⟩ := hb
  obtain ⟨s, hs⟩ := hab
  refine ⟨r + s, ?_⟩
  dsimp [pairAverage]
  omega

theorem odd_pairAverage_of_two_pow_dvd {a b : ℤ} {t : ℕ}
    (hb : Odd b) (ht : 2 ≤ t) (hab : (2 : ℤ) ^ t ∣ a - b) :
    Odd (pairAverage a b) := by
  apply odd_pairAverage hb
  have hpow : (2 : ℤ) ^ 2 ∣ (2 : ℤ) ^ t := pow_dvd_pow 2 ht
  exact (show (4 : ℤ) ∣ (2 : ℤ) ^ t from hpow).trans hab

theorem normScalar_halving (u : ℤ) {t : ℕ} (ht : 1 ≤ t) :
    (2 : ℤ) ^ (2 * t) * u ^ 2 =
      4 * ((2 : ℤ) ^ (2 * (t - 1)) * u ^ 2) := by
  have hexp : 2 * t = 2 * (t - 1) + 2 := by omega
  rw [hexp, pow_add]
  ring

/-- Literal paired coefficients on the quotient of a cyclic group of even
order. Integer divisibility is proved separately before this is used. -/
noncomputable def halvePairs {m : ℕ} [NeZero m] (T : Elem ℤ (2 * m)) : Elem ℤ m :=
  ofCoeffs fun j => pairAverage (T.coeff (j.val : ZMod (2 * m)))
    (T.coeff ((j.val + m : ℕ) : ZMod (2 * m)))

@[simp] theorem halvePairs_apply {m : ℕ} [NeZero m] (T : Elem ℤ (2 * m))
    (j : ZMod m) :
    (halvePairs T).coeff j = pairAverage (T.coeff (j.val : ZMod (2 * m)))
      (T.coeff ((j.val + m : ℕ) : ZMod (2 * m))) := rfl

theorem halvePairs_odd {m : ℕ} [NeZero m] (T : Elem ℤ (2 * m))
    (hodd : ∀ j, Odd (T.coeff j))
    (hpair : ∀ j : ZMod m, (4 : ℤ) ∣
      T.coeff (j.val : ZMod (2 * m)) - T.coeff ((j.val + m : ℕ) : ZMod (2 * m))) :
    ∀ j, Odd ((halvePairs T).coeff j) := by
  intro j
  exact odd_pairAverage (hodd _) (hpair j)

/-- Cancellation takes place in each integer coefficient. A cyclic group
ring has zero divisors, which are irrelevant to this scalar cancellation. -/
theorem four_smul_cancel {m : ℕ} {S T : Elem ℤ m}
    (h : (4 : ℤ) • S = (4 : ℤ) • T) : S = T := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro j
  have hj := congrArg (fun f : Elem ℤ m => f.coeff j) h
  change 4 * S.coeff j = 4 * T.coeff j at hj
  omega

theorem norm_of_double_norm {m : ℕ} [NeZero m] (T : Elem ℤ m) (c : ℤ)
    (h : ((2 : ℤ) • T) * ringStar ((2 : ℤ) • T) = scalar m (4 * c)) :
    T * ringStar T = scalar m c := by
  have hstar : ringStar ((2 : ℤ) • T) = (2 : ℤ) • ringStar T := by
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro j
    change star ((2 : ℤ) * T.coeff (-j)) = (2 : ℤ) * star (T.coeff (-j))
    simp only [star_trivial]
  have hfour : ((2 : ℤ) • T) * ringStar ((2 : ℤ) • T) =
      (4 : ℤ) • (T * ringStar T) := by
    rw [hstar, smul_mul_assoc, mul_smul_comm, smul_smul]
    rfl
  have hscalar : scalar m (4 * c) = (4 : ℤ) • scalar m c := by
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro j
    change (scalar m (4 * c)).coeff j = (4 : ℤ) * (scalar m c).coeff j
    by_cases hj : j = 0 <;> simp [scalar_apply, hj]
  apply four_smul_cancel
  rw [← hfour, h, hscalar]

/-- Odd coefficients make the literal projected fiber sums exactly twice the
integer averages. This is an identity for the actual cyclic quotient map. -/
theorem cyclicProjection_eq_two_smul_halvePairs {m : ℕ} [NeZero m]
    (h : m ∣ 2 * m) (T : Elem ℤ (2 * m)) (hodd : ∀ j, Odd (T.coeff j)) :
    cyclicProjection ℤ h T = (2 : ℤ) • halvePairs T := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro j
  rw [cyclicProjection_double_apply (NeZero.pos m) h]
  change _ = 2 * pairAverage _ _
  exact (two_mul_pairAverage (hodd _) (hodd _)).symm

/-- Projecting and dividing by two divides the scalar norm by four. All
coefficient and star identities are consequences of the actual quotient. -/
theorem halvePairs_norm {m : ℕ} [NeZero m] [NeZero (2 * m)]
    (T : Elem ℤ (2 * m)) (c : ℤ) (hodd : ∀ j, Odd (T.coeff j))
    (hnorm : T * ringStar T = scalar (2 * m) (4 * c)) :
    halvePairs T * ringStar (halvePairs T) = scalar m c := by
  have hdiv : m ∣ 2 * m := ⟨2, Nat.mul_comm 2 m⟩
  have hproj := cyclicProjection_norm hdiv hnorm
  rw [cyclicProjection_eq_two_smul_halvePairs hdiv T hodd] at hproj
  exact norm_of_double_norm (halvePairs T) c hproj

/-- Algebraic halving with paired divisibility. In the dyadic case, cyclotomic
evaluation supplies this divisibility from the norm equation. -/
theorem halvePairs_odd_norm_of_pair_divisibility {m : ℕ} [NeZero m] [NeZero (2 * m)]
    (t u : ℕ) (T : Elem ℤ (2 * m)) (ht : 2 ≤ t)
    (hodd : ∀ j, Odd (T.coeff j))
    (hnorm : T * ringStar T = scalar (2 * m) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ))
    (hpair : ∀ j : ZMod m, (2 : ℤ) ^ t ∣
      T.coeff (j.val : ZMod (2 * m)) - T.coeff ((j.val + m : ℕ) : ZMod (2 * m))) :
    (∀ j, Odd ((halvePairs T).coeff j)) ∧
      halvePairs T * ringStar (halvePairs T) =
        scalar m ((2 ^ (2 * (t - 1)) * u ^ 2 : ℕ) : ℤ) := by
  constructor
  · intro j
    exact odd_pairAverage_of_two_pow_dvd (hodd _) ht (hpair j)
  · apply halvePairs_norm T _ hodd
    have hs : ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ) =
        4 * ((2 ^ (2 * (t - 1)) * u ^ 2 : ℕ) : ℤ) := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        normScalar_halving (u : ℤ) (show 1 ≤ t by omega)
    rw [← hs]
    exact hnorm

/-- The actual dyadic order-halving step. The paired divisibility is supplied
by cyclotomic evaluation and localization, not assumed in this statement.
The constructed witness is the literal paired average `halvePairs`. -/
theorem exists_odd_halving (k t u : ℕ) (T : Elem ℤ (2 ^ (k + 1)))
    (ht : 2 ≤ t) (hu : Odd u) (hodd : ∀ j, Odd (T.coeff j))
    (hnorm : T * ringStar T =
      scalar (2 ^ (k + 1)) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ)) :
    ∃ U : Elem ℤ (2 ^ k), (∀ j, Odd (U.coeff j)) ∧
      U * ringStar U = scalar (2 ^ k) ((2 ^ (2 * (t - 1)) * u ^ 2 : ℕ) : ℤ) := by
  have hstep (n : ℕ) [NeZero n] (hn : n = 2 * 2 ^ k) (S : Elem ℤ n)
      (hS : ∀ j, Odd (S.coeff j))
      (hnormS : S * ringStar S = scalar n ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ))
      (hpair : ∀ j : ZMod (2 ^ k), (2 : ℤ) ^ t ∣
        S.coeff (j.val : ZMod n) - S.coeff ((j.val + 2 ^ k : ℕ) : ZMod n)) :
      ∃ U : Elem ℤ (2 ^ k), (∀ j, Odd (U.coeff j)) ∧
        U * ringStar U = scalar (2 ^ k) ((2 ^ (2 * (t - 1)) * u ^ 2 : ℕ) : ℤ) := by
    subst n
    exact ⟨halvePairs S,
      halvePairs_odd_norm_of_pair_divisibility t u S ht hS hnormS hpair⟩
  exact hstep (2 ^ (k + 1)) (pow_succ' 2 k) T hodd hnorm
    (dyadic_difference_dvd k t u T hu hnorm)

end CirculantHadamard

end OAI
