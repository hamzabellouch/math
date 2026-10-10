import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.PolynomialHomogeneousScaling
import OAI.Analysis.RieszRectifiability.Kernel.ShrinkingSchwartzLocalization

namespace OAI

/-!
# Leading homogeneous terms under dilation

Along an expanding sequence of positive radii, normalization by the total
degree makes lower-degree powers vanish and preserves the top-degree power.
Applying this limit to the finite homogeneous decomposition of a polynomial
recovers its leading homogeneous component pointwise.
-/

namespace RieszRectifiability

noncomputable section

open Filter Topology

def polynomialExpansionRadius (j : ℕ) : ℝ := (j : ℝ) + 2

theorem polynomialExpansionRadius_pos (j : ℕ) : 0 < polynomialExpansionRadius j := by
  unfold polynomialExpansionRadius
  positivity

theorem inverse_pow_mul_pow_of_le (z : ℂ) (hz : z ≠ 0) (n N : ℕ) (hn : n ≤ N) :
    (z ^ N)⁻¹ * z ^ n = (z⁻¹) ^ (N - n) := by
  calc
    _ = (z ^ (N - n) * z ^ n)⁻¹ * z ^ n := by rw [← pow_add, Nat.sub_add_cancel hn]
    _ = _ := by
      rw [mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hz), mul_one, inv_pow]

theorem inverse_polynomialExpansionRadius_tendsto :
    Tendsto (fun j => (polynomialExpansionRadius j : ℂ)⁻¹) atTop (𝓝 0) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp shrinkingRadius_tendsto
  simpa only [Function.comp_def, shrinkingRadius, polynomialExpansionRadius, Complex.ofReal_zero,
    Complex.ofReal_inv] using! h

theorem polynomial_scale_coefficient_tendsto (N n : ℕ) (hn : n ≤ N) :
    Tendsto (fun j => ((polynomialExpansionRadius j : ℂ) ^ N)⁻¹ *
      (polynomialExpansionRadius j : ℂ) ^ n) atTop (𝓝 (if n = N then 1 else 0)) := by
  have hz : ∀ j, (polynomialExpansionRadius j : ℂ) ≠ 0 := fun j =>
    Complex.ofReal_ne_zero.mpr (polynomialExpansionRadius_pos j).ne'
  by_cases he : n = N
  · subst n
    simpa only [ite_eq_left rfl, inv_mul_cancel₀ (pow_ne_zero _ (hz _))] using!
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))
  · have hpos : N - n ≠ 0 := by omega
    have h := inverse_polynomialExpansionRadius_tendsto.pow (N - n)
    simpa only [inverse_pow_mul_pow_of_le _ (hz _) n N hn, ite_eq_right he, zero_pow hpos] using! h

theorem polynomial_normalized_dilation_tendsto {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (x : Ambient d) :
    Tendsto (fun j => ((polynomialExpansionRadius j : ℂ) ^ P.totalDegree)⁻¹ *
      MvPolynomial.eval (fun i => ((polynomialExpansionRadius j • x) i : ℂ)) P)
      atTop (𝓝 (MvPolynomial.eval (fun i => (x i : ℂ))
        (MvPolynomial.homogeneousComponent P.totalDegree P))) := by
  classical
  have hlim := tendsto_finsetSum (Finset.range (P.totalDegree + 1))
    (fun n hn => (polynomial_scale_coefficient_tendsto P.totalDegree n
      (Nat.le_of_lt_succ (Finset.mem_range.mp hn))).mul_const
        (MvPolynomial.eval (fun i => (x i : ℂ)) (MvPolynomial.homogeneousComponent n P)))
  have heq : (fun j => ((polynomialExpansionRadius j : ℂ) ^ P.totalDegree)⁻¹ *
      MvPolynomial.eval (fun i => ((polynomialExpansionRadius j • x) i : ℂ)) P) =
      (fun j => ∑ n ∈ Finset.range (P.totalDegree + 1),
        (((polynomialExpansionRadius j : ℂ) ^ P.totalDegree)⁻¹ *
          (polynomialExpansionRadius j : ℂ) ^ n) *
          MvPolynomial.eval (fun i => (x i : ℂ)) (MvPolynomial.homogeneousComponent n P)) := by
    funext j
    rw [polynomial_scaled_eval_homogeneous_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [heq]
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
    Nat.lt_succ_self, ite_true] using! hlim

end

end RieszRectifiability

end OAI
