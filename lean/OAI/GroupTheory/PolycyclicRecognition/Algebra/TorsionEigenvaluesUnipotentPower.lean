import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Nilpotent.Basic

namespace OAI

/-! # A common unipotent power from torsion eigenvalues

A finite product synchronizes the eigenvalue periods. The split
characteristic polynomial then divides a power of `X^m - 1`; evaluating at
the operator proves nilpotence without choosing a Jordan basis.
-/

noncomputable section
namespace PolycyclicRecognition
open Polynomial
open scoped Polynomial

theorem finite_torsion_common_power {A : Type*} [Monoid A]
    (s : Finset A) (hs : ∀ a ∈ s, ∃ n : ℕ, 0 < n ∧ a ^ n = 1) :
    ∃ m : ℕ, 0 < m ∧ ∀ a ∈ s, a ^ m = 1 := by
  classical
  have h : ∀ a : A, ∃ n : ℕ, 0 < n ∧ (a ∈ s → a ^ n = 1) := by
    intro a
    by_cases ha : a ∈ s
    · obtain ⟨n, hn, he⟩ := hs a ha
      exact ⟨n, hn, fun _ => he⟩
    · exact ⟨1, by omega, fun h => (ha h).elim⟩
  choose n hn he using h
  refine ⟨∏ a ∈ s, n a, Finset.prod_pos (fun a _ => hn a), ?_⟩
  intro a ha
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n ha
  rw [hk, pow_mul, he a ha, one_pow]

theorem split_polynomial_dvd_power_of_vanishing {K : Type*} [Field K]
    (p q : K[X]) (hp : p.Splits) (hm : p.Monic)
    (hq : ∀ z ∈ p.roots, q.eval z = 0) : p ∣ q ^ p.roots.card := by
  have hdiv := Multiset.prod_dvd_prod_of_dvd
    (fun z : K => Polynomial.X - Polynomial.C z) (fun _ => q)
    (fun z hz => Polynomial.dvd_iff_isRoot.mpr (hq z hz))
  rw [← hp.eq_prod_roots_of_monic hm] at hdiv
  simpa using hdiv

theorem unipotent_power_of_torsion_eigenvalues
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (T : Module.End K V) (hsplit : T.charpoly.Splits)
    (hroots : ∀ z, T.HasEigenvalue z → ∃ n : ℕ, 0 < n ∧ z ^ n = 1) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent (T ^ m - 1) := by
  classical
  obtain ⟨m, hm, hperiod⟩ := finite_torsion_common_power T.charpoly.roots.toFinset (by
    intro z hz
    exact hroots z ((Module.End.hasEigenvalue_iff_isRoot_charpoly T z).mpr
      ((Polynomial.mem_roots T.charpoly_monic.ne_zero).mp (Multiset.mem_toFinset.mp hz))))
  let q : K[X] := Polynomial.X ^ m - 1
  have hdiv : T.charpoly ∣ q ^ T.charpoly.roots.card :=
    split_polynomial_dvd_power_of_vanishing T.charpoly q hsplit T.charpoly_monic (by
      intro z hz
      simp only [q, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, hperiod z (Multiset.mem_toFinset.mpr hz), sub_self])
  obtain ⟨r, hr⟩ := hdiv
  refine ⟨m, hm, T.charpoly.roots.card, ?_⟩
  have he := congrArg (Polynomial.aeval T) hr
  simpa only [q, map_pow, map_sub, Polynomial.aeval_X, map_one, map_mul,
    LinearMap.aeval_self_charpoly, zero_mul] using he

end PolycyclicRecognition

end

end OAI
