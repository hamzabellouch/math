import OAI.Combinatorics.Crossing.TwoTriangleUnisolvence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module
open scoped BigOperators

abbrev BiExponent (s : ℕ) := Fin s × Fin s

def biOfCoeffs (s : ℕ) (c : BiExponent s → ℝ) : BiPoly :=
  ∑ a : Fin s, single ℝ a.val (∑ b : Fin s, single ℝ b.val (c (a,b)))

theorem biCoeff_biOfCoeffs (s : ℕ) (c : BiExponent s → ℝ) (a b : Fin s) :
    biCoeff (biOfCoeffs s c) a.val b.val = c (a,b) := by
  simp [biCoeff, biOfCoeffs, coeff_sum, Finsupp.finsetSum_apply, Finsupp.single_apply, Fin.val_inj]

theorem biOfCoeffs_injective (s : ℕ) : Function.Injective (biOfCoeffs s) := by
  intro c d h
  funext ab
  have hh := congrArg (fun p => biCoeff p ab.1.val ab.2.val) h
  simpa only [biCoeff_biOfCoeffs] using hh

theorem biOfCoeffs_bounded (s : ℕ) (c : BiExponent s → ℝ) :
    BiBounded s s (biOfCoeffs s c) := by
  constructor
  · apply bounded_sum
    intro a ha
    exact bounded_single a.isLt _
  · intro n k hk
    simp only [biOfCoeffs, coeff_sum, Finsupp.finsetSum_apply, coeff_single,
      Finsupp.single_apply]
    apply Finset.sum_eq_zero
    intro a ha
    split_ifs with hna
    · simp only [coeff_sum, Finsupp.finsetSum_apply, coeff_single, Finsupp.single_apply]
      apply Finset.sum_eq_zero
      intro b hb
      rw [ite_eq_right (by omega)]
    · rfl

theorem biEval_biOfCoeffs (s : ℕ) (c : BiExponent s → ℝ) (u v : ℝ) :
    biEval u v (biOfCoeffs s c) = ∑ a : Fin s, ∑ b : Fin s,
      (u^a.val * v^b.val) * c (a,b) := by
  simp [biOfCoeffs, biEval, eval_single, smul_eq_mul, Finset.mul_sum, mul_assoc]

end Zarankiewicz

end

end OAI
