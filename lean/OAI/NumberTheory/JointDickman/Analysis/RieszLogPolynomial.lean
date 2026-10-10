import OAI.NumberTheory.JointDickman.Analysis.LogRieszBounds

namespace OAI

/-! # Smooth finite logarithmic polynomials used to remove Riesz smoothing -/
namespace JointDickman
open Finset

noncomputable def rieszLogPolynomial (b : ℕ → ℝ) (z : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (K+1), b j*logRieszMonomial (z-1-j) x

noncomputable def rieszLogDerivative (b : ℕ → ℝ) (z : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (K+1), b j*logRieszDerivative (z-1-j) x

noncomputable def rieszLogSecondDerivative (b : ℕ → ℝ) (z : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (K+1), b j*logRieszSecondDerivative (z-1-j) x

theorem hasDerivAt_rieszLogPolynomial (b : ℕ → ℝ) (z : ℝ) (K : ℕ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (rieszLogPolynomial b z K) (rieszLogDerivative b z K x) x := by
  exact HasDerivAt.fun_sum (fun (j : ℕ) (_ : j ∈ range (K+1)) =>
    (hasDerivAt_logRieszMonomial (z-1-j) hx).const_mul (b j))

theorem hasDerivAt_rieszLogDerivative (b : ℕ → ℝ) (z : ℝ) (K : ℕ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (rieszLogDerivative b z K) (rieszLogSecondDerivative b z K x) x := by
  exact HasDerivAt.fun_sum (fun (j : ℕ) (_ : j ∈ range (K+1)) =>
    (hasDerivAt_logRieszDerivative (z-1-j) hx).const_mul (b j))

theorem rieszLogSecondDerivative_uniform_bound (b : ℕ → ℝ) (z : ℝ) (K : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x t : ℝ, 0 < x → 2 ≤ Real.log x → t ∈ Set.Icc (x/2) (2*x) →
      |rieszLogSecondDerivative b z K t| ≤ M*(Real.log x)^(z-1) := by
  let C : ℝ → ℝ := fun β =>
    2*(2:ℝ)^(|β|)+3*|β| *(2:ℝ)^(|β-1|)+|β*(β-1)| *(2:ℝ)^(|β-2|)
  refine ⟨∑ j ∈ range (K+1), |b j| *C (z-1-j),sum_nonneg (fun j _ => by dsimp [C]; positivity),?_⟩
  intro x t hx hlog ht
  unfold rieszLogSecondDerivative
  calc
    _ ≤ ∑ j ∈ range (K+1), |b j*logRieszSecondDerivative (z-1-j) t| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (K+1), (|b j| *C (z-1-j))*(Real.log x)^(z-1) := by
      apply sum_le_sum
      intro j _
      rw [abs_mul]
      have hc : 0 ≤ C (z-1-j) := by dsimp [C]; positivity
      calc
        _ ≤ |b j| *(C (z-1-j)*(Real.log x)^(z-1-j)) :=
          mul_le_mul_of_nonneg_left (logRieszSecondDerivative_bound (z-1-j) hx hlog ht) (abs_nonneg _)
        _ ≤ |b j| *(C (z-1-j)*(Real.log x)^(z-1)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply mul_le_mul_of_nonneg_left _ hc
          exact Real.rpow_le_rpow_of_exponent_le (by linarith)
            (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
        _ = _ := by ring
    _ = _ := by rw [sum_mul]

end JointDickman

end OAI
