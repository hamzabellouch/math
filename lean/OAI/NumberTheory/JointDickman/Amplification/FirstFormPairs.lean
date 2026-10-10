import OAI.NumberTheory.JointDickman.Arithmetic.WeightedDivisorEdge

namespace OAI

/-! # The actual arithmetic weight of each unequal-coefficient pair -/

namespace JointDickman
open Finset

noncomputable def firstFormPairWeight (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (D A E : Finset ℕ) (m : ℕ) : ℝ :=
  firstFormWeight B L τ C u D m *
    (regularCoefficientWeight B L τ C (∏ p ∈ A, p) *
      arithmeticResidueWeight B L τ C (((∏ p ∈ A, p)*m+1)/(∏ p ∈ D, p)) *
        v (∏ p ∈ A, p) (∏ p ∈ D, p)) *
    (regularCoefficientWeight B L τ C (∏ p ∈ E, p) *
      arithmeticResidueWeight B L τ C (((∏ p ∈ E, p)*m+1)/(∏ p ∈ D, p)) *
        v (∏ p ∈ E, p) (∏ p ∈ D, p))

noncomputable def firstFormPairEnergy (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) (D A E : Finset ℕ) : ℝ :=
  ∑ m ∈ range N, firstFormWeight B L τ C u D m *
    (star (firstFormAtom B L τ C v J N D m A) * firstFormAtom B L τ C v J N D m E).re

theorem real_weighted_pair (r s : ℝ) (z w : ℂ) :
    (star ((r : ℂ)*z) * ((s : ℂ)*w)).re = r*s*(star z*w).re := by
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.conj_re, Complex.conj_im]
  ring

theorem firstFormPairEnergy_as_old (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) (D A E : Finset ℕ) :
    firstFormPairEnergy B L τ C u v J N D A E =
      ∑ m ∈ divisorEdgeOld (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) N,
        firstFormPairWeight B L τ C u v D A E m *
          (star (J ((∏ p ∈ A, p)*m)) * J ((∏ p ∈ E, p)*m)).re := by
  classical
  unfold firstFormPairEnergy divisorEdgeOld
  rw [sum_filter]
  apply sum_congr rfl
  intro m _
  unfold firstFormAtom
  dsimp only
  by_cases ha : (∏ p ∈ A, p)*m < N ∧ (∏ p ∈ D, p) ∣ (∏ p ∈ A, p)*m+1
  · by_cases hb : (∏ p ∈ E, p)*m < N ∧ (∏ p ∈ D, p) ∣ (∏ p ∈ E, p)*m+1
    · rw [ite_eq_left ha,ite_eq_left hb,ite_eq_left ⟨ha.1,hb.1,ha.2,hb.2⟩,real_weighted_pair]
      unfold firstFormPairWeight
      ring
    · have hh : ¬ ((∏ p ∈ A, p)*m < N ∧ (∏ p ∈ E, p)*m < N ∧
        (∏ p ∈ D, p) ∣ (∏ p ∈ A, p)*m+1 ∧ (∏ p ∈ D, p) ∣ (∏ p ∈ E, p)*m+1) :=
        fun h => hb ⟨h.2.1,h.2.2.2⟩
      simp only [ite_eq_right hb,ite_eq_right hh,mul_zero,Complex.zero_re]
  · have hh : ¬ ((∏ p ∈ A, p)*m < N ∧ (∏ p ∈ E, p)*m < N ∧
        (∏ p ∈ D, p) ∣ (∏ p ∈ A, p)*m+1 ∧ (∏ p ∈ D, p) ∣ (∏ p ∈ E, p)*m+1) :=
        fun h => ha ⟨h.1,h.2.2.1⟩
    simp only [ite_eq_right ha,ite_eq_right hh,star_zero,zero_mul,Complex.zero_re,mul_zero]

theorem firstFormOffDiagonal_eq_pairSum (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) :
    firstFormOffDiagonal B L τ C u v J N =
      (∑ D ∈ (auxiliaryPrimes B).powerset, ∑ A ∈ (auxiliaryPrimes B).powerset,
        ∑ E ∈ (auxiliaryPrimes B).powerset,
          if A = E then 0 else firstFormPairEnergy B L τ C u v J N D A E)/(N : ℝ) := by
  classical
  unfold firstFormOffDiagonal firstFormPairEnergy
  congr 1
  rw [sum_product]
  apply sum_congr rfl
  intro D _
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  rw [sum_comm]
  apply sum_congr rfl
  intro E _
  by_cases h : A = E <;> simp only [h,ite_true,ite_false,mul_zero,sum_const_zero]

end JointDickman

end OAI
