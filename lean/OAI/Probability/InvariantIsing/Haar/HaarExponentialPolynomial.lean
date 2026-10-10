import OAI.Probability.InvariantIsing.Haar.HaarPolynomialEntropyBound

namespace OAI

/-! Positive polynomial truncations of an exponential observable. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def haarExpPolynomial {N : ℕ} (n : ℕ) (p : MatrixPolynomial N) : MatrixPolynomial N :=
  ∑ k ∈ Finset.range (n+1), ((Nat.factorial k : ℝ)⁻¹) • p^k

lemma haarExpPolynomial_eval {N : ℕ} (n : ℕ) (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (haarExpPolynomial n p) =
      ∑ k ∈ Finset.range (n+1), (matrixPolynomialEval M p)^k/(Nat.factorial k : ℝ) := by
  simp only [haarExpPolynomial,map_sum,map_smul,map_pow,smul_eq_mul,div_eq_mul_inv,mul_comm]

lemma haarExpPolynomial_derivation {N : ℕ} (n : ℕ) (p : MatrixPolynomial N)
    (A : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialDerivation A (haarExpPolynomial (n+1) p) =
      haarExpPolynomial n p*matrixPolynomialDerivation A p := by
  unfold haarExpPolynomial
  rw [Finset.sum_range_succ']
  simp only [map_add,map_sum,Derivation.map_smul_of_tower,pow_zero,
    Derivation.map_one_eq_zero,smul_zero,add_zero]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  have hf : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hcoef : ((Nat.factorial (k+1) : ℝ)⁻¹)*((k+1:ℕ):ℝ) =
      (Nat.factorial k : ℝ)⁻¹ := by
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    field_simp
  rw [Derivation.leibniz_pow]
  simp only [Nat.add_sub_cancel]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  change (Nat.factorial (k+1) : ℝ)⁻¹ •
    (((k+1:ℕ):ℝ) • (p^k*matrixPolynomialDerivation A p)) = _
  rw [smul_smul,hcoef,smul_mul_assoc]

end InvariantIsing

end

end OAI
