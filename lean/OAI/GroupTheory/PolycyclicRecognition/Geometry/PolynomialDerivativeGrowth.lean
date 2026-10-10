import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformPolynomialGrowth
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMinor
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Derivative bounds on growing polynomial input cubes -/

noncomputable section
namespace PolycyclicRecognition

open MvPolynomial Set Metric
open scoped BigOperators

theorem continuous_pderiv_evaluation {P : Type*} [TopologicalSpace P] {m : ℕ}
    (p : P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a, (p a).totalDegree ≤ D)
    (heval : ∀ x, Continuous (fun a => eval x (p a))) (j : Fin m) (x : Fin m → ℝ) :
    Continuous (fun a => eval x (pderiv j (p a))) := by
  apply continuous_polynomial_evaluation_of_coefficients (fun a => pderiv j (p a)) D
    (fun a => (totalDegree_pderiv_le (p a) j).trans ((Nat.sub_le _ _).trans (hD a)))
  intro s
  simp only [coeff_pderiv]
  exact (continuous_polynomial_coefficients p D hD heval _).mul continuous_const

theorem norm_clm_pi_domain_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {m : ℕ} (L : (Fin m → ℝ) →L[ℝ] V) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, ‖L (Pi.single j 1)‖ ≤ B) : ‖L‖ ≤ (m : ℝ) * B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hB)
  intro x
  have he : L x = ∑ j, x j • L (Pi.single j 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  rw [he]
  calc
    ‖∑ j, x j • L (Pi.single j 1)‖ ≤ ∑ j, ‖x j • L (Pi.single j 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, ‖x‖ * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (norm_le_pi_norm x j) (hb j) (norm_nonneg _) (norm_nonneg _)
    _ = (m : ℝ) * B * ‖x‖ := by simp; ring

def polynomialMapDifferential {m n : ℕ} (p : Fin n → MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => polynomialDifferential (p i) x)

theorem hasFDerivAt_polynomialMap {m n : ℕ} (p : Fin n → MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) :
    HasFDerivAt (fun y i => eval y (p i)) (polynomialMapDifferential p x) x := by
  exact hasFDerivAt_pi.mpr (fun i => hasFDerivAt_mvPolynomial_eval (p i) x)

@[simp] theorem polynomialMapDifferential_basis {m n : ℕ}
    (p : Fin n → MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) (i : Fin n) (j : Fin m) :
    polynomialMapDifferential p x (Pi.single j 1) i = eval x (pderiv j (p i)) :=
  polynomialDifferential_basis (p i) x j

theorem norm_polynomialMapDifferential_le {m n : ℕ}
    (p : Fin n → MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i j, |eval x (pderiv j (p i))| ≤ B) :
    ‖polynomialMapDifferential p x‖ ≤ (m : ℝ) * B := by
  apply norm_clm_pi_domain_le _ hB
  intro j
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  simpa only [polynomialMapDifferential_basis, Real.norm_eq_abs] using hb i j

theorem norm_polynomialDifferential_le {m : ℕ}
    (p : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, |eval x (pderiv j p)| ≤ B) :
    ‖polynomialDifferential p x‖ ≤ (m : ℝ) * B := by
  apply norm_clm_pi_domain_le _ hB
  intro j
  simpa only [polynomialDifferential_basis, Real.norm_eq_abs] using hb j

theorem uniform_polynomial_map_derivative_bounds
    {P : Type*} [TopologicalSpace P] {m n : ℕ}
    (p : P → Fin n → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a i, (p a i).totalDegree ≤ D)
    (heval : ∀ i x, Continuous (fun a => eval x (p a i)))
    (S : Set P) (hS : IsCompact S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ S, ∀ R : ℝ, 0 ≤ R →
      (∀ x, ‖x‖ ≤ R → ‖polynomialMapDifferential (p a) x‖ ≤ C * (1 + R) ^ (m * D)) ∧
      ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
        ‖polynomialMapDifferential (p a) x - polynomialMapDifferential (p a) y‖ ≤
          C * (1 + R) ^ (m * D) * dist x y := by
  let p₁ := fun j : Fin n × Fin m => fun a => pderiv j.2 (p a j.1)
  have hD₁ (j : Fin n × Fin m) (a : P) : (p₁ j a).totalDegree ≤ D :=
    (totalDegree_pderiv_le (p a j.1) j.2).trans ((Nat.sub_le _ _).trans (hD a j.1))
  have he₁ (j : Fin n × Fin m) (x : Fin m → ℝ) :
      Continuous (fun a => eval x (p₁ j a)) :=
    continuous_pderiv_evaluation (fun a => p a j.1) D (fun a => hD a j.1)
      (heval j.1) j.2 x
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_uniform_finite_polynomial_growth p₁ D hD₁ he₁ S hS
  let p₂ := fun j : (Fin n × Fin m) × Fin m => fun a => pderiv j.2 (p₁ j.1 a)
  have hD₂ (j : (Fin n × Fin m) × Fin m) (a : P) : (p₂ j a).totalDegree ≤ D :=
    (totalDegree_pderiv_le (p₁ j.1 a) j.2).trans ((Nat.sub_le _ _).trans (hD₁ j.1 a))
  have he₂ (j : (Fin n × Fin m) × Fin m) (x : Fin m → ℝ) :
      Continuous (fun a => eval x (p₂ j a)) :=
    continuous_pderiv_evaluation (p₁ j.1) D (hD₁ j.1) (he₁ j.1) j.2 x
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_uniform_finite_polynomial_growth p₂ D hD₂ he₂ S hS
  let C := max 1 (max ((m : ℝ) * C₁) ((m : ℝ) ^ 2 * C₂))
  have hc₁ : (m : ℝ) * C₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hc₂ : (m : ℝ) ^ 2 * C₂ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro a ha R hR
  have hpow : 0 ≤ (1 + R) ^ (m * D) := pow_nonneg (by linarith) _
  have hb₁R (i : Fin n) (j : Fin m) (x : Fin m → ℝ) (hx : ‖x‖ ≤ R) :
      |eval x (pderiv j (p a i))| ≤ C₁ * (1 + R) ^ (m * D) :=
    (hb₁ (i, j) a ha x).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) _) (by linarith))
  have hb₂R (i : Fin n) (j k : Fin m) (x : Fin m → ℝ) (hx : ‖x‖ ≤ R) :
      |eval x (pderiv k (pderiv j (p a i)))| ≤ C₂ * (1 + R) ^ (m * D) :=
    (hb₂ ((i, j), k) a ha x).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) _) (by linarith))
  constructor
  · intro x hx
    calc
      _ ≤ (m : ℝ) * (C₁ * (1 + R) ^ (m * D)) :=
        norm_polynomialMapDifferential_le _ _ (mul_nonneg (by linarith) hpow) (fun i j => hb₁R i j x hx)
      _ ≤ C * (1 + R) ^ (m * D) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hc₁ hpow
  · intro x y hx hy
    have hscalar (i : Fin n) (j : Fin m) :
        |eval x (pderiv j (p a i)) - eval y (pderiv j (p a i))| ≤
          (m : ℝ) * (C₂ * (1 + R) ^ (m * D)) * dist x y := by
      have h := (convex_closedBall (0 : Fin m → ℝ) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun u _ => (hasFDerivAt_mvPolynomial_eval (pderiv j (p a i)) u).hasFDerivWithinAt)
        (fun u hu => norm_polynomialDifferential_le _ _ (mul_nonneg (by linarith) hpow)
          (fun k => hb₂R i j k u (by simpa only [mem_closedBall, dist_zero_right] using hu)))
        (show y ∈ closedBall 0 R by simpa using hy) (show x ∈ closedBall 0 R by simpa using hx)
      simpa only [Real.norm_eq_abs, dist_eq_norm] using h
    have hB : 0 ≤ (m : ℝ) * (C₂ * (1 + R) ^ (m * D)) * dist x y := by positivity
    calc
      _ ≤ (m : ℝ) * ((m : ℝ) * (C₂ * (1 + R) ^ (m * D)) * dist x y) := by
        apply norm_clm_pi_domain_le _ hB
        intro j
        apply (pi_norm_le_iff_of_nonneg hB).mpr
        intro i
        simpa only [sub_apply, Pi.sub_apply,
          polynomialMapDifferential_basis, Real.norm_eq_abs] using hscalar i j
      _ = ((m : ℝ) ^ 2 * C₂) * (1 + R) ^ (m * D) * dist x y := by ring
      _ ≤ C * (1 + R) ^ (m * D) * dist x y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₂ hpow) dist_nonneg

end PolycyclicRecognition

end

end OAI
