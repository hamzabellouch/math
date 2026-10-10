import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.GaussianEnclosure
import Mathlib.Algebra.Polynomial.Inductions

namespace OAI

/-! # Polynomial semantics for integer coefficient enclosures

Lists are in ascending coefficient order. The recursive semantics keeps all
roundoff radii, including those of coefficients whose centers cancel.
-/

open Polynomial

namespace DefocusingNLS
namespace GaussianEnclosure

def zero : GaussianEnclosure := ⟨0, 0⟩

theorem zero_sound : zero.Encloses 0 := by simp [Encloses, zero]

theorem zero_encloses_iff (z : ℂ) : zero.Encloses z ↔ z = 0 := by
  simp [Encloses, zero]

/-- An enclosure for every coefficient, with exact zero beyond the list. -/
def EnclosesPolynomial : List GaussianEnclosure → Polynomial ℂ → Prop
  | [], p => p = 0
  | a :: as, p => ∃ z q, a.Encloses z ∧ EnclosesPolynomial as q ∧ p = C z + X * q

def addPolynomial : List GaussianEnclosure → List GaussianEnclosure → List GaussianEnclosure
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => add a b :: addPolynomial as bs

def scalePolynomial (a : GaussianEnclosure) (bs : List GaussianEnclosure) : List GaussianEnclosure :=
  bs.map (mul a)

def mulPolynomial : List GaussianEnclosure → List GaussianEnclosure → List GaussianEnclosure
  | [], _ => []
  | a :: as, bs => addPolynomial (scalePolynomial a bs) (zero :: mulPolynomial as bs)

def negPolynomial (as : List GaussianEnclosure) : List GaussianEnclosure := as.map neg

def subPolynomial (as bs : List GaussianEnclosure) : List GaussianEnclosure :=
  addPolynomial as (negPolynomial bs)

def conjPolynomial (as : List GaussianEnclosure) : List GaussianEnclosure := as.map conj

theorem addPolynomial_sound {as bs : List GaussianEnclosure} {p q : Polynomial ℂ}
    (hp : EnclosesPolynomial as p) (hq : EnclosesPolynomial bs q) :
    EnclosesPolynomial (addPolynomial as bs) (p + q) := by
  induction as generalizing bs p q with
  | nil =>
    change p = 0 at hp
    subst p
    simpa [addPolynomial] using hq
  | cons a as ih =>
    cases bs with
    | nil =>
      change q = 0 at hq
      subst q
      simpa [addPolynomial] using hp
    | cons b bs =>
      obtain ⟨x, p', hx, hp', rfl⟩ := hp
      obtain ⟨y, q', hy, hq', rfl⟩ := hq
      refine ⟨x + y, p' + q', add_sound hx hy, ih hp' hq', ?_⟩
      simp only [map_add]
      ring

theorem scalePolynomial_sound {a : GaussianEnclosure} {as : List GaussianEnclosure}
    {z : ℂ} {p : Polynomial ℂ} (hz : a.Encloses z) (hp : EnclosesPolynomial as p) :
    EnclosesPolynomial (scalePolynomial a as) (C z * p) := by
  induction as generalizing p with
  | nil =>
    change p = 0 at hp
    subst p
    simp [EnclosesPolynomial, scalePolynomial]
  | cons b bs ih =>
    obtain ⟨x, q, hx, hq, rfl⟩ := hp
    refine ⟨z * x, C z * q, mul_sound hz hx, ih hq, ?_⟩
    simp only [map_mul]
    ring

theorem shiftPolynomial_sound {as : List GaussianEnclosure} {p : Polynomial ℂ}
    (hp : EnclosesPolynomial as p) : EnclosesPolynomial (zero :: as) (X * p) :=
  ⟨0, p, zero_sound, hp, by simp⟩

theorem mulPolynomial_sound {as bs : List GaussianEnclosure} {p q : Polynomial ℂ}
    (hp : EnclosesPolynomial as p) (hq : EnclosesPolynomial bs q) :
    EnclosesPolynomial (mulPolynomial as bs) (p * q) := by
  induction as generalizing p with
  | nil =>
    change p = 0 at hp
    subst p
    simp [mulPolynomial, EnclosesPolynomial]
  | cons a as ih =>
    obtain ⟨z, p', hz, hp', rfl⟩ := hp
    have h := addPolynomial_sound (scalePolynomial_sound hz hq)
      (shiftPolynomial_sound (ih hp'))
    have he : (C z + X * p') * q = C z * q + X * (p' * q) := by ring
    rw [he]
    exact h

theorem negPolynomial_sound {as : List GaussianEnclosure} {p : Polynomial ℂ}
    (hp : EnclosesPolynomial as p) : EnclosesPolynomial (negPolynomial as) (-p) := by
  induction as generalizing p with
  | nil =>
    change p = 0 at hp
    subst p
    simp [EnclosesPolynomial, negPolynomial]
  | cons a as ih =>
    obtain ⟨z, q, hz, hq, rfl⟩ := hp
    refine ⟨-z, -q, neg_sound hz, ih hq, ?_⟩
    simp only [map_neg]
    ring

theorem subPolynomial_sound {as bs : List GaussianEnclosure} {p q : Polynomial ℂ}
    (hp : EnclosesPolynomial as p) (hq : EnclosesPolynomial bs q) :
    EnclosesPolynomial (subPolynomial as bs) (p - q) := by
  simpa only [subPolynomial, sub_eq_add_neg] using addPolynomial_sound hp (negPolynomial_sound hq)

theorem conjPolynomial_sound {as : List GaussianEnclosure} {p : Polynomial ℂ}
    (hp : EnclosesPolynomial as p) :
    EnclosesPolynomial (conjPolynomial as) (p.map (starRingEnd ℂ)) := by
  induction as generalizing p with
  | nil =>
    change p = 0 at hp
    subst p
    simp [EnclosesPolynomial, conjPolynomial]
  | cons a as ih =>
    obtain ⟨z, q, hz, hq, rfl⟩ := hp
    exact ⟨star z, q.map (starRingEnd ℂ), conj_sound hz, ih hq, by simp⟩

theorem coefficient_sound {as : List GaussianEnclosure} {p : Polynomial ℂ}
    (hp : EnclosesPolynomial as p) (n : ℕ) :
    (as[n]?.getD zero).Encloses (p.coeff n) := by
  induction as generalizing p n with
  | nil =>
    change p = 0 at hp
    subst p
    simpa using zero_sound
  | cons a as ih =>
    obtain ⟨z, q, hz, hq, rfl⟩ := hp
    cases n with
    | zero => simpa using hz
    | succ n => simpa [coeff_X_mul] using ih hq n

/-- Coefficientwise semantics permits truncation only when the actual discarded
coefficients vanish, regardless of the size of their computed radii. -/
theorem enclosesPolynomial_of_coefficients (as : List GaussianEnclosure) (p : Polynomial ℂ)
    (h : ∀ n, (as[n]?.getD zero).Encloses (p.coeff n)) : EnclosesPolynomial as p := by
  induction as generalizing p with
  | nil =>
    apply Polynomial.ext
    intro n
    exact (zero_encloses_iff _).mp (h n)
  | cons a as ih =>
    refine ⟨p.coeff 0, p.divX, ?_, ?_, ?_⟩
    · simpa using h 0
    · apply ih
      intro n
      simpa only [coeff_divX, List.getElem?_cons_succ] using h (n + 1)
    · exact (add_comm _ _).trans (X_mul_divX_add p) |>.symm

theorem enclosesPolynomial_iff_coefficients (as : List GaussianEnclosure) (p : Polynomial ℂ) :
    EnclosesPolynomial as p ↔ ∀ n, (as[n]?.getD zero).Encloses (p.coeff n) :=
  ⟨fun hp n => coefficient_sound hp n, enclosesPolynomial_of_coefficients as p⟩

theorem truncatePolynomial_sound {as : List GaussianEnclosure} {p : Polynomial ℂ}
    (hp : EnclosesPolynomial as p) (N : ℕ) (hN : ∀ n, N ≤ n → p.coeff n = 0) :
    EnclosesPolynomial (as.take N) p := by
  apply enclosesPolynomial_of_coefficients
  intro n
  by_cases hn : n < N
  · simpa [List.getElem?_take, hn] using coefficient_sound hp n
  · have hn' : N ≤ n := Nat.le_of_not_lt hn
    simpa [List.getElem?_take, hn, hN n hn'] using zero_sound

end GaussianEnclosure
end DefocusingNLS

end OAI
