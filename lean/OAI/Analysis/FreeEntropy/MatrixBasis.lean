import OAI.Analysis.FreeEntropy.MatrixChart

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 def hermitianBasis {d : ℕ} (j k : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  if j=k then Matrix.single j j 1 else if j<k then
    ((Real.sqrt 2 : ℂ)⁻¹) • (Matrix.single j k 1 + Matrix.single k j 1)
  else (Complex.I * (Real.sqrt 2 : ℂ)⁻¹) • (Matrix.single k j 1 - Matrix.single j k 1)
 theorem hermitianBasis_self {d : ℕ} (j : Fin d) : hermitianBasis j j = Matrix.single j j 1 := by
  simp [hermitianBasis]
 theorem sqrt_two_complex_sq : (Real.sqrt 2 : ℂ)^2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)
 theorem inv_sqrt_two_complex_sq : ((Real.sqrt 2 : ℂ)⁻¹)^2 = (1/2 : ℂ) := by
  rw [inv_pow, sqrt_two_complex_sq, one_div]
 theorem basis_pair_contract {d : ℕ} (j k : Fin d) (D : Matrix (Fin d) (Fin d) ℂ) :
    hermitianBasis j k * D * hermitianBasis j k + hermitianBasis k j * D * hermitianBasis k j =
      Matrix.single j k 1 * D * Matrix.single k j 1 + Matrix.single k j 1 * D * Matrix.single j k 1 := by
  by_cases hjk : j=k
  · subst k; simp [hermitianBasis]
  have hcalc (A B : Matrix (Fin d) (Fin d) ℂ) :
      (((Real.sqrt 2 : ℂ)⁻¹) • (A+B)) * D * (((Real.sqrt 2 : ℂ)⁻¹) • (A+B)) +
      ((Complex.I*(Real.sqrt 2 : ℂ)⁻¹) • (A-B)) * D * ((Complex.I*(Real.sqrt 2 : ℂ)⁻¹) • (A-B)) =
      A*D*B + B*D*A := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    have hs : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1/2 : ℂ) := by
      simpa only [pow_two] using inv_sqrt_two_complex_sq
    have hi : (Complex.I*(Real.sqrt 2 : ℂ)⁻¹) * (Complex.I*(Real.sqrt 2 : ℂ)⁻¹) = -(1/2 : ℂ) := by
      calc
        _ = Complex.I^2 * ((Real.sqrt 2 : ℂ)⁻¹)^2 := by ring
        _ = _ := by rw [Complex.I_sq, inv_sqrt_two_complex_sq]; ring
    rw [hs,hi]
    simp only [add_mul,mul_add,sub_mul,mul_sub]
    module
  rcases lt_or_gt_of_ne hjk with h | h
  · simpa only [hermitianBasis, ite_eq_right hjk, ite_eq_right (Ne.symm hjk), ite_eq_left h,
      ite_eq_right (not_lt_of_gt h)] using hcalc (Matrix.single j k 1) (Matrix.single k j 1)
  · simpa only [hermitianBasis, ite_eq_right hjk, ite_eq_right (Ne.symm hjk), ite_eq_left h,
      ite_eq_right (not_lt_of_gt h), add_comm] using hcalc (Matrix.single k j 1) (Matrix.single j k 1)
 theorem hermitianBasis_contract {d : ℕ} (D : Matrix (Fin d) (Fin d) ℂ) :
    (∑ j, ∑ k, hermitianBasis j k * D * hermitianBasis j k) = Matrix.trace D • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have hp := congrArg (fun f : Fin d → Fin d → Matrix (Fin d) (Fin d) ℂ => ∑ j, ∑ k, f j k)
    (funext (fun j => funext (fun k => basis_pair_contract j k D)))
  simp only [sum_add_distrib] at hp
  have hswap : (∑ j : Fin d, ∑ k : Fin d, hermitianBasis k j * D * hermitianBasis k j) =
      ∑ j : Fin d, ∑ k : Fin d, hermitianBasis j k * D * hermitianBasis j k := sum_comm
  have hswap' : (∑ j : Fin d, ∑ k : Fin d, Matrix.single k j 1 * D * Matrix.single j k 1) =
      ∑ j : Fin d, ∑ k : Fin d, Matrix.single j k 1 * D * Matrix.single k j 1 := sum_comm
  rw [hswap,hswap'] at hp
  have he : (∑ j : Fin d, ∑ k : Fin d, Matrix.single j k 1 * D * Matrix.single k j 1) =
      Matrix.trace D • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    ext a b
    simp only [Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.sum_apply, Matrix.single_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hab : a=b
    · subst b; simp [Matrix.trace]
    · simp only [hab, ite_false, mul_zero]
      apply sum_eq_zero
      intro j _
      simp only [ite_eq_right (show ¬(j=a ∧ j=b) from fun h => hab (h.1.symm.trans h.2)), sum_const_zero]
  rw [he] at hp
  ext a b
  have hc := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => A a b) hp
  simp only [Matrix.add_apply] at hc
  linear_combination hc / 2
end FiniteEntropySeparation

end

end OAI
