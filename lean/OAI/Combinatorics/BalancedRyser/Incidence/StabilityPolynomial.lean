import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Tactic

namespace OAI

namespace Balanced.StabilityPolynomial

open Polynomial

variable {K : Type*} [Field K]

theorem derivatives_eq_zero_of_coprime_wronskian
    {f g : K[X]} (hcop : IsCoprime f g)
    (hW : derivative f * g - derivative g * f = 0) :
    derivative f = 0 ∧ derivative g = 0 := by
  have hW' : wronskian g f = 0 := by
    simpa only [wronskian, mul_comm] using hW
  exact (hcop.symm.wronskian_eq_zero_iff.mp hW').symm

theorem eq_C_of_derivative_eq_zero_of_natDegree_lt_char
    {p : ℕ} [CharP K p] {f : K[X]}
    (hdeg : f.natDegree < p) (hd : derivative f = 0) :
    f = C (f.coeff 0) := by
  apply eq_C_of_natDegree_eq_zero
  by_contra hn
  have hpos : 0 < f.natDegree := Nat.pos_of_ne_zero hn
  have hsucc : f.natDegree - 1 + 1 = f.natDegree := Nat.sub_add_cancel hpos
  have hcast : (f.natDegree : K) ≠ 0 := by
    intro hz
    exact Nat.not_dvd_of_pos_of_lt hpos hdeg
      ((CharP.cast_eq_zero_iff K p f.natDegree).mp hz)
  have hcoeff : f.coeff f.natDegree * (f.natDegree : K) = 0 := by
    have h := congrArg (fun r : K[X] => r.coeff (f.natDegree - 1)) hd
    simpa only [coeff_derivative, ← Nat.cast_add_one, hsucc, coeff_zero] using h
  have hzero : f = 0 := by
    apply leadingCoeff_eq_zero.mp
    exact (mul_eq_zero.mp hcoeff).resolve_right hcast
  exact hn (by simp [hzero])

theorem constants_of_coprime_wronskian_of_natDegree_lt_char
    {p : ℕ} [CharP K p] {f g : K[X]}
    (hcop : IsCoprime f g)
    (hf : f.natDegree < p) (hg : g.natDegree < p)
    (hW : derivative f * g - derivative g * f = 0) :
    f = C (f.coeff 0) ∧ g = C (g.coeff 0) := by
  obtain ⟨hdf, hdg⟩ := derivatives_eq_zero_of_coprime_wronskian hcop hW
  exact ⟨eq_C_of_derivative_eq_zero_of_natDegree_lt_char hf hdf,
    eq_C_of_derivative_eq_zero_of_natDegree_lt_char hg hdg⟩

end Balanced.StabilityPolynomial

end OAI
