import OAI.Analysis.HyperbolicCones.ConeRoots
import OAI.Analysis.HyperbolicCones.ZeroPolynomial

namespace OAI

noncomputable section

open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator

namespace Paper256

theorem charpoly_eval_eigenvalue (n : ℕ) (X : Sym n) (i : Fin n) :
    (X : Mat n ℝ).charpoly.eval ((sym_isHermitian X).eigenvalues i) = 0 := by
  rw [(sym_isHermitian X).charpoly_eq]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, RCLike.ofReal_real_eq_id, id_eq]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

theorem charpoly_real_roots_nonnegative (n : ℕ) (X : Sym n)
    (hX : (X : Mat n ℝ).PosSemidef) (t : ℝ)
    (ht : (X : Mat n ℝ).charpoly.eval t = 0) : 0 ≤ t := by
  rw [(sym_isHermitian X).charpoly_eq] at ht
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, RCLike.ofReal_real_eq_id, id_eq, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero] at ht
  obtain ⟨i, rfl⟩ := ht
  exact hX.eigenvalues_nonneg i

theorem cone_zero_slice (X Z : Sym 4) : ((X, Z), (0 : Fin 3 → ℝ)) ∈ cone ↔
    (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef := by
  rw [cone_iff_nonnegative_real_roots, linePolynomial_zero_parameter]
  constructor
  · intro h
    constructor
    · apply (sym_isHermitian X).posSemidef_iff_eigenvalues_nonneg.mpr
      intro i
      apply h ((sym_isHermitian X).eigenvalues i)
      simp [charpoly_eval_eigenvalue]
    · apply (sym_isHermitian Z).posSemidef_iff_eigenvalues_nonneg.mpr
      intro i
      apply h ((sym_isHermitian Z).eigenvalues i)
      simp [charpoly_eval_eigenvalue]
  · rintro ⟨hX, hZ⟩ t ht
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, mul_eq_zero,
      pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)] at ht
    exact ht.elim (charpoly_real_roots_nonnegative 4 X hX t)
      (charpoly_real_roots_nonnegative 4 Z hZ t)

end Paper256

end

end OAI
