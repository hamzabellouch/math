import OAI.NumberTheory.JointDickman.Amplification.AmplificationFirstForm

namespace OAI

/-! # The diagonal is bounded by one weight cap times the linear mass -/

namespace JointDickman
open Finset

open Classical in
noncomputable def firstFormAtom (B L : ℕ) (τ C : ℝ) (v : ℕ → ℕ → ℝ)
    (J : ℕ → ℂ) (N : ℕ) (D : Finset ℕ) (m : ℕ) (A : Finset ℕ) : ℂ :=
  let a := ∏ p ∈ A, p
  let c := ∏ p ∈ D, p
  if a*m < N ∧ c ∣ a*m+1 then
    ((regularCoefficientWeight B L τ C a *
      arithmeticResidueWeight B L τ C ((a*m+1)/c) * v a c : ℝ) : ℂ) * J (a*m)
  else 0

noncomputable def firstFormDiagonal (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) : ℝ :=
  (∑ i ∈ (auxiliaryPrimes B).powerset ×ˢ range N,
    firstFormWeight B L τ C u i.1 i.2 *
      ∑ A ∈ (auxiliaryPrimes B).powerset, ‖firstFormAtom B L τ C v J N i.1 i.2 A‖^2) / (N : ℝ)

noncomputable def firstFormMass (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (φ : ℕ → ℝ) (N : ℕ) : ℝ :=
  (firstDivisorForm B L τ C u v (fun _ => 1) (fun n => (φ n : ℂ)) N).re

theorem firstFormAtom_diagonal_bound (B L : ℕ) (τ C : ℝ) (v : ℕ → ℕ → ℝ)
    (J : ℕ → ℂ) (φ : ℕ → ℝ) (N : ℕ) (Q : ℝ)
    (hv : ∀ a c, v a c ∈ Set.Icc (0 : ℝ) 1)
    (hJ : ∀ n, ‖J n‖^2 ≤ 4*φ n)
    (hcap : ∀ a m, regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C m ≤ Q)
    (D : Finset ℕ) (m : ℕ) (A : Finset ℕ) :
    ‖firstFormAtom B L τ C v J N D m A‖^2 ≤
      4*Q*(firstFormAtom B L τ C v (fun n => (φ n : ℂ)) N D m A).re := by
  classical
  unfold firstFormAtom
  dsimp only
  split_ifs with h
  · let a := ∏ p ∈ A, p
    let c := ∏ p ∈ D, p
    let x := regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C ((a*m+1)/c)
    have hx : 0 ≤ x := mul_nonneg (regularCoefficientWeight_nonneg B L τ C _)
      (regularResidueWeight_nonneg B L τ C _)
    have hv0 := (hv a c).1
    have hv1 := (hv a c).2
    have hcoef : x*v a c ≤ Q := (mul_le_of_le_one_right hx hv1).trans (hcap a ((a*m+1)/c))
    have hz : 0 ≤ x*v a c := mul_nonneg hx hv0
    have hsq : (x*v a c)^2 ≤ Q*(x*v a c) := by nlinarith
    have hh := mul_le_mul hsq (hJ (a*m)) (sq_nonneg _) (mul_nonneg (le_trans hz hcoef) hz)
    change ‖((x*v a c : ℝ) : ℂ) * J (a*m)‖^2 ≤
      4*Q*(((x*v a c : ℝ) : ℂ) * (φ (a*m) : ℂ)).re
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  · simp

/-- Bounding one regular coefficient/residue factor pays only one Q. -/
theorem firstFormDiagonal_le (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (φ : ℕ → ℝ) (N : ℕ) (Q : ℝ)
    (hu : ∀ c, 0 ≤ u c) (hv : ∀ a c, v a c ∈ Set.Icc (0 : ℝ) 1)
    (hJ : ∀ n, ‖J n‖^2 ≤ 4*φ n)
    (hcap : ∀ a m, regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C m ≤ Q) :
    firstFormDiagonal B L τ C u v J N ≤ 4*Q*firstFormMass B L τ C u v φ N := by
  classical
  have hp (D : Finset ℕ) (m : ℕ) :
      ∑ A ∈ (auxiliaryPrimes B).powerset, ‖firstFormAtom B L τ C v J N D m A‖^2 ≤
        4*Q*(firstFormInner B L τ C v (fun n => (φ n : ℂ)) N D m).re := by
    unfold firstFormInner
    rw [Complex.re_sum, mul_sum]
    exact sum_le_sum fun A _ => firstFormAtom_diagonal_bound B L τ C v J φ N Q hv hJ hcap D m A
  unfold firstFormDiagonal firstFormMass firstDivisorForm
  simp only [star_one, mul_one]
  simp only [Complex.div_natCast_re, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left (hp i.1 i.2) (firstFormWeight_nonneg B L τ C u hu i.1 i.2)
  nlinarith

end JointDickman

end OAI
