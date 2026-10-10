import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace OAI


namespace SiegelZeros.W10

open Module

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

def generators (a b : K) : Fin 4 → K := ![1, a, b, a * b]

theorem coefficients_eq_zero_of_sign_automorphisms
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (σ τ : K ≃ₐ[ℚ] K)
    (hσa : σ a = -a) (hσb : σ b = b)
    (hτa : τ a = a) (hτb : τ b = -b)
    (r s t u : ℚ)
    (h : (r : K) + (s : K) * a + (t : K) * b + (u : K) * (a * b) = 0) :
    r = 0 ∧ s = 0 ∧ t = 0 ∧ u = 0 := by
  have hσ := congrArg σ h
  have hτ := congrArg τ h
  have hστ := congrArg σ hτ
  simp only [map_add, map_mul, map_ratCast, map_zero, hσa, hσb] at hσ
  simp only [map_add, map_mul, map_ratCast, map_zero, hτa, hτb] at hτ
  simp only [map_add, map_mul, map_ratCast, map_zero, map_neg,
    hσa, hσb, hτa, hτb] at hστ
  have hr : (r : K) = 0 := by linear_combination (h + hσ + hτ + hστ) / 4
  have hs : (s : K) * a = 0 := by linear_combination (h - hσ + hτ - hστ) / 4
  have ht : (t : K) * b = 0 := by linear_combination (h + hσ - hτ - hστ) / 4
  have hu : (u : K) * (a * b) = 0 := by
    linear_combination (h - hσ - hτ + hστ) / 4
  have hs' : (s : K) = 0 := (mul_eq_zero.mp hs).resolve_right ha
  have ht' : (t : K) = 0 := (mul_eq_zero.mp ht).resolve_right hb
  have hu' : (u : K) = 0 := (mul_eq_zero.mp hu).resolve_right (mul_ne_zero ha hb)
  exact ⟨Rat.cast_eq_zero.mp hr, Rat.cast_eq_zero.mp hs',
    Rat.cast_eq_zero.mp ht', Rat.cast_eq_zero.mp hu'⟩

theorem generators_linearIndependent
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (σ τ : K ≃ₐ[ℚ] K)
    (hσa : σ a = -a) (hσb : σ b = b)
    (hτa : τ a = a) (hτb : τ b = -b) :
    LinearIndependent ℚ (generators a b) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  have hsum : (g 0 : K) + (g 1 : K) * a + (g 2 : K) * b +
      (g 3 : K) * (a * b) = 0 := by
    simpa [generators, Fin.sum_univ_succ, Algebra.smul_def,
      add_assoc] using hg
  obtain ⟨h0, h1, h2, h3⟩ := coefficients_eq_zero_of_sign_automorphisms
    a b ha hb σ τ hσa hσb hτa hτb (g 0) (g 1) (g 2) (g 3) hsum
  intro i
  fin_cases i <;> assumption

noncomputable def generatorsBasis
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (σ τ : K ≃ₐ[ℚ] K)
    (hσa : σ a = -a) (hσb : σ b = b)
    (hτa : τ a = a) (hτb : τ b = -b)
    (hdegree : Module.finrank ℚ K = 4) : Basis (Fin 4) ℚ K :=
  basisOfLinearIndependentOfCardEqFinrank
    (generators_linearIndependent a b ha hb σ τ hσa hσb hτa hτb)
    (by simpa using hdegree.symm)

theorem generatorsBasis_apply
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (σ τ : K ≃ₐ[ℚ] K)
    (hσa : σ a = -a) (hσb : σ b = b)
    (hτa : τ a = a) (hτb : τ b = -b)
    (hdegree : Module.finrank ℚ K = 4) (i : Fin 4) :
    generatorsBasis a b ha hb σ τ hσa hσb hτa hτb hdegree i = generators a b i := by
  simp [generatorsBasis]

omit [CharZero K] [Algebra ℚ K] in
theorem isIntegral_of_square_eq_int (a : K) (d : ℤ) (ha : a ^ 2 = (d : K)) :
    IsIntegral ℤ a := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  rw [ha]
  exact isIntegral_algebraMap

omit [CharZero K] [Algebra ℚ K] in
theorem generators_isIntegral (a b : K) (d : ℤ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = (2 : K)) (i : Fin 4) :
    IsIntegral ℤ (generators a b i) := by
  have hai := isIntegral_of_square_eq_int a d ha
  have hbi := isIntegral_of_square_eq_int b 2 (by simpa using hb)
  fin_cases i
  · exact isIntegral_one
  · exact hai
  · exact hbi
  · exact hai.mul hbi

end SiegelZeros.W10

end OAI
