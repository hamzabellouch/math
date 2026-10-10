import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorNonlinearUniqueness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorJetLimit

namespace OAI

/-! Different truncation orders represent the same outgoing asymptotic data. -/

open Polynomial Set
namespace DefocusingNLS

theorem radialExteriorExpansion_coeff_initial (ν : ℂ) (n : ℕ) (m : ℂ)
    (j k i : ℕ) (hjk : j ≤ k) (hi : i ≤ j) :
    (radialExteriorExpansion ν n m k).coeff i=(radialExteriorExpansion ν n m j).coeff i := by
  induction k with
  | zero =>
    have hj : j=0 := by omega
    subst j
    rfl
  | succ k ih =>
    by_cases hj : j=k+1
    · subst j; rfl
    · have hjk' : j ≤ k := by omega
      exact (radialExteriorExpansion_coeff_stable ν n m k i (hi.trans hjk')).trans (ih hjk')

theorem radialExteriorExpansion_difference_dvd (ν : ℂ) (n : ℕ) (m : ℂ)
    (j k : ℕ) (hjk : j ≤ k) :
    X^j ∣ radialExteriorExpansion ν n m k-radialExteriorExpansion ν n m j := by
  apply X_pow_dvd_iff.mpr
  intro i hi
  rw [coeff_sub,radialExteriorExpansion_coeff_initial ν n m j k i hjk (by omega),sub_self]

theorem radialPolynomialEuler_preserves_divisibility (P : ℂ[X]) (j : ℕ) (hP : X^j ∣ P) :
    X^j ∣ radialPolynomialEuler P := by
  apply X_pow_dvd_iff.mpr
  intro i hi
  rw [radialPolynomialEuler_coeff,X_pow_dvd_iff.mp hP i hi,mul_zero]

theorem radialPolynomial_factor_decay (P R : ℂ[X]) (j : ℕ) (hP : P=X^j*R)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖radialExteriorPolynomialFunction P t‖ ≤
      ‖boundedRadialPolynomial R‖*Real.exp (-(2*(j : ℝ))*t) := by
  have he : Real.exp (-2*t)^j=Real.exp (-(2*(j : ℝ))*t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hb : ‖radialExteriorPolynomialFunction R t‖ ≤ ‖boundedRadialPolynomial R‖ := by
    rw [← boundedRadialPolynomial_nonneg R t ht]
    exact (boundedRadialPolynomial R).norm_coe_le_norm t
  simp only [radialExteriorPolynomialFunction,hP,eval_mul,eval_pow,eval_X,norm_mul,
    norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  rw [he]
  exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq (mul_comm _ _)

theorem radialPolynomialJet_factor_decay (P : ℂ[X]) (j : ℕ) (hP : X^j ∣ P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t →
      ‖radialPolynomialJet P t‖ ≤ C*Real.exp (-(2*(j : ℝ))*t) := by
  obtain ⟨R,hR⟩ := hP
  obtain ⟨Q,hQ⟩ := radialPolynomialEuler_preserves_divisibility P j ⟨R,hR⟩
  refine ⟨‖boundedRadialPolynomial R‖+‖boundedRadialPolynomial Q‖,by positivity,?_⟩
  intro t ht
  apply max_le
  · exact (radialPolynomial_factor_decay P R j hR t ht).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg _)) (Real.exp_pos _).le)
  · exact (radialPolynomial_factor_decay (radialPolynomialEuler P) Q j hQ t ht).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg _)) (Real.exp_pos _).le)

theorem radialExteriorExpansion_jet_difference_decay (ν : ℂ) (n : ℕ) (m : ℂ)
    (j k : ℕ) (hjk : j ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t →
      ‖radialPolynomialJet (radialExteriorExpansion ν n m k) t-
        radialPolynomialJet (radialExteriorExpansion ν n m j) t‖ ≤
          C*Real.exp (-(2*(j : ℝ))*t) := by
  obtain ⟨C,hC,hbound⟩ := radialPolynomialJet_factor_decay
    (radialExteriorExpansion ν n m k-radialExteriorExpansion ν n m j) j
    (radialExteriorExpansion_difference_dvd ν n m j k hjk)
  refine ⟨C,hC,?_⟩
  intro t ht
  convert hbound t ht using 1
  congr 1
  apply Prod.ext <;> simp [radialPolynomialJet,radialExteriorPolynomialFunction,
    radialPolynomialEuler,derivative_sub,mul_sub]

end DefocusingNLS

end OAI
