import OAI.Analysis.HyperbolicCones.PolynomialBasic

namespace OAI

noncomputable section

open scoped BigOperators

universe u

namespace Paper256

theorem homogeneous_eval_smul {σ : Type u} [Fintype σ]
    (p : MvPolynomial σ ℝ) (d : ℕ) (hp : p.IsHomogeneous d)
    (s : ℝ) (v : σ → ℝ) :
    MvPolynomial.eval (s • v) p = s ^ d * MvPolynomial.eval v p := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hd : a.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hp (MvPolynomial.mem_support_iff.mp ha)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← Finsupp.degree_eq_sum, hd]
  ring

theorem coordinates_smul (s : ℝ) (x : Ambient) :
    coordinates (s • x) = s • coordinates x := by
  funext i
  rcases i with (i | i) | i <;> rfl

theorem coordinates_sub (x z : Ambient) :
    coordinates (x - z) = coordinates x - coordinates z := by
  funext i
  rcases i with (i | i) | i <;> rfl

theorem polynomial_eval_smul (s : ℝ) (x : Ambient) :
    MvPolynomial.eval (coordinates (s • x)) polynomial =
      s ^ 20 * MvPolynomial.eval (coordinates x) polynomial := by
  rw [coordinates_smul]
  exact homogeneous_eval_smul polynomial 20 polynomial_homogeneous s (coordinates x)

theorem polynomial_eval_neg (x : Ambient) :
    MvPolynomial.eval (coordinates (-x)) polynomial =
      MvPolynomial.eval (coordinates x) polynomial := by
  have h := polynomial_eval_smul (-1) x
  norm_num at h
  exact h

end Paper256

end

end OAI
