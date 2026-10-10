import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootLeafHopf
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.RingTheory.Polynomial.RationalRoot

namespace OAI

/-!
# The algebraic obstruction to exceptional returns

EKL (Annals of Mathematics 164 (2006), Proposition 5.2) excludes an
integral special-linear matrix with exactly one repeated eigenvalue and
no eigenvalues equal to ±1. The first step is that a unique repeated
root of a rational polynomial must be rational: a distinct Galois
conjugate would also be a common root of the polynomial and its derivative.
-/

noncomputable section
open Polynomial
open scoped Classical

namespace DukePrimeDegree

theorem unique_common_root_is_rational
    (p : ℚ[X]) (hp : p ≠ 0) (x : ℂ)
    (hx : aeval x p = 0) (hdx : aeval x p.derivative = 0)
    (hunique : ∀ y : ℂ, aeval y p = 0 → aeval y p.derivative = 0 → y = x) :
    ∃ q : ℚ, (q : ℂ) = x := by
  have hi : IsIntegral ℚ x := (show IsAlgebraic ℚ x from ⟨p, hp, hx⟩).isIntegral
  have hs : IsSeparable ℚ x := (minpoly.irreducible hi).separable
  have hmem : x ∈ (⊥ : Subalgebra ℚ ℂ) := by
    by_contra hn
    obtain ⟨y, hxy, hconj⟩ :=
      (notMem_iff_exists_ne_and_isConjRoot hs (IsAlgClosed.splits _)).mp hn
    have hpy : minpoly ℚ y ∣ p := by
      rw [← hconj]
      exact minpoly.dvd ℚ x hx
    have hdpy : minpoly ℚ y ∣ p.derivative := by
      rw [← hconj]
      exact minpoly.dvd ℚ x hdx
    exact hxy (hunique y (minpoly.dvd_iff.mp hpy) (minpoly.dvd_iff.mp hdpy)).symm
  exact Algebra.mem_bot.mp hmem

theorem rational_root_of_monic_unit_constant
    (p : ℤ[X]) (hp : p.Monic) (hc : IsUnit (p.coeff 0))
    {q : ℚ} (hq : aeval q p = 0) : q = 1 ∨ q = -1 := by
  obtain ⟨a, hqa, ha⟩ := exists_integer_of_is_root_of_monic hp hq
  have hu : IsUnit a := isUnit_of_dvd_unit ha hc
  have habs : |a| = 1 := Int.isUnit_iff_abs_eq.mp hu
  rcases le_total 0 a with hnonneg | hnonpos
  · left
    rw [abs_of_nonneg hnonneg] at habs
    simpa only [habs, map_one] using hqa
  · right
    rw [abs_of_nonpos hnonpos] at habs
    have ha : a = -1 := by omega
    simpa only [ha, map_neg, map_one] using hqa

/-- The repeated-root obstruction in EKL Proposition 5.2, in polynomial form. -/
theorem unique_common_root_of_monic_unit_constant
    (p : ℤ[X]) (hp : p.Monic) (hc : IsUnit (p.coeff 0)) (x : ℂ)
    (hx : aeval x p = 0) (hdx : aeval x p.derivative = 0)
    (hunique : ∀ y : ℂ, aeval y p = 0 → aeval y p.derivative = 0 → y = x) :
    x = 1 ∨ x = -1 := by
  let pQ := p.map (algebraMap ℤ ℚ)
  have heval (r : ℤ[X]) (y : ℂ) :
      aeval y (r.map (algebraMap ℤ ℚ)) = aeval y r := by
    exact (aeval_eq_aeval_map (by ext a; simp) r y).symm
  have hpQ : pQ ≠ 0 := (hp.map (algebraMap ℤ ℚ)).ne_zero
  have hxQ : aeval x pQ = 0 := by rw [heval]; exact hx
  have hdxQ : aeval x pQ.derivative = 0 := by
    change aeval x (p.map (algebraMap ℤ ℚ)).derivative = 0
    rw [derivative_map, heval]
    exact hdx
  have huniqQ : ∀ y : ℂ, aeval y pQ = 0 → aeval y pQ.derivative = 0 → y = x := by
    intro y hy hyd
    apply hunique y
    · rwa [heval] at hy
    · change aeval y (p.map (algebraMap ℤ ℚ)).derivative = 0 at hyd
      rwa [derivative_map, heval] at hyd
  obtain ⟨q, hq⟩ := unique_common_root_is_rational pQ hpQ x hxQ hdxQ huniqQ
  have hqr : aeval q p = 0 := by
    apply (algebraMap ℚ ℂ).injective
    rw [map_zero]
    change (IsScalarTower.toAlgHom ℤ ℚ ℂ) (aeval q p) = 0
    rw [← aeval_algHom_apply]
    change aeval (q : ℂ) p = 0
    rwa [hq]
  rcases rational_root_of_monic_unit_constant p hp hc hqr with h | h
  · left
    rw [← hq, h]
    norm_num
  · right
    rw [← hq, h]
    norm_num

/-- A unique multiple complex root of a monic integer unit polynomial
must be one of the two rational units. -/
theorem unique_repeated_root_of_monic_unit_constant
    (p : ℤ[X]) (hp : p.Monic) (hc : IsUnit (p.coeff 0)) (x : ℂ)
    (hx : 1 < (p.map (algebraMap ℤ ℂ)).rootMultiplicity x)
    (hunique : ∀ y : ℂ, 1 < (p.map (algebraMap ℤ ℂ)).rootMultiplicity y → y = x) :
    x = 1 ∨ x = -1 := by
  let P := p.map (algebraMap ℤ ℂ)
  have hP : P ≠ 0 := (hp.map (algebraMap ℤ ℂ)).ne_zero
  have heval (r : ℤ[X]) (y : ℂ) : (r.map (algebraMap ℤ ℂ)).eval y = aeval y r := by
    rw [eval_map]
    rfl
  have hroots := (one_lt_rootMultiplicity_iff_isRoot hP).mp hx
  apply unique_common_root_of_monic_unit_constant p hp hc x
  · simpa only [P, IsRoot, heval] using hroots.1
  · simpa only [P, derivative_map, IsRoot, heval] using hroots.2
  · intro y hy hyd
    apply hunique y
    apply (one_lt_rootMultiplicity_iff_isRoot hP).mpr
    constructor
    · simpa only [P, IsRoot, heval] using hy
    · simpa only [P, derivative_map, IsRoot, heval] using hyd

/-- Polynomial form of EKL Proposition 5.2 for integral special-linear matrices. -/
theorem integer_sl_unique_repeated_root {n : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin n) ℤ) (x : ℂ)
    (hx : 1 < (g.val.charpoly.map (algebraMap ℤ ℂ)).rootMultiplicity x)
    (hunique : ∀ y : ℂ, 1 < (g.val.charpoly.map (algebraMap ℤ ℂ)).rootMultiplicity y → y = x) :
    x = 1 ∨ x = -1 := by
  apply unique_repeated_root_of_monic_unit_constant g.val.charpoly g.val.charpoly_monic _ x hx hunique
  apply isUnit_of_dvd_one
  refine ⟨(-1 : ℤ) ^ Fintype.card (Fin n), ?_⟩
  have h := g.val.det_eq_sign_charpoly_coeff
  rw [g.property] at h
  simpa only [mul_comm] using h

end DukePrimeDegree

end

end OAI
