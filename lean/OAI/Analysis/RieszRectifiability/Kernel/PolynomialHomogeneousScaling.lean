import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem homogeneous_polynomial_eval_mul {σ : Type*} (P : MvPolynomial σ ℂ)
    (n : ℕ) (hP : P.IsHomogeneous n) (r : ℂ) (x : σ → ℂ) :
    MvPolynomial.eval (fun i => r * x i) P = r ^ n * MvPolynomial.eval x P := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hd := hP (MvPolynomial.mem_support_iff.mp hs)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum] at hd
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem homogeneous_polynomial_eval_real_smul {d n : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (hP : P.IsHomogeneous n) (r : ℝ) (x : Ambient d) :
    MvPolynomial.eval (fun j => ((r • x) j : ℂ)) P =
      (r : ℂ) ^ n * MvPolynomial.eval (fun j => (x j : ℂ)) P := by
  have hc : (fun j => ((r • x) j : ℂ)) = (fun j => (r : ℂ) * (x j : ℂ)) := by
    funext j
    change ((r * x j : ℝ) : ℂ) = (r : ℂ) * (x j : ℂ)
    exact Complex.ofReal_mul _ _
  rw [hc]
  exact homogeneous_polynomial_eval_mul P n hP (r : ℂ) (fun j => (x j : ℂ))

theorem polynomial_scaled_eval_homogeneous_sum {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (r : ℝ) (x : Ambient d) :
    MvPolynomial.eval (fun j => ((r • x) j : ℂ)) P =
      ∑ n ∈ Finset.range (P.totalDegree + 1), (r : ℂ) ^ n *
        MvPolynomial.eval (fun j => (x j : ℂ)) (MvPolynomial.homogeneousComponent n P) := by
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent P]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact homogeneous_polynomial_eval_real_smul _
    (MvPolynomial.homogeneousComponent_isHomogeneous n P) r x

end

end RieszRectifiability

end OAI
