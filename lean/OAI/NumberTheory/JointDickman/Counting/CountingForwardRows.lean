import OAI.NumberTheory.JointDickman.Counting.CountingArithmeticCoefficient
import OAI.NumberTheory.JointDickman.Counting.FiniteForwardLagSum
import OAI.NumberTheory.JointDickman.Counting.CoarseCountingRows

namespace OAI

/-! # The periodic graph row as a finite-feature convolution -/
namespace JointDickman
open Finset Classical

noncomputable def countingForwardRow (F : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M u : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (z : ℕ → ℂ) (i : Fin M) : ℂ :=
  ∑ k : Fin M, if i < k then
    (countingSiteWithSeries F P m B L T H M τ C c D σ i k
      ⟨coefficientPrimeSet B (u+(i.val+1)),by simp [coefficientPrimeSet]⟩
      ⟨coefficientPrimeSet B (u+(k.val+1)),by simp [coefficientPrimeSet]⟩ : ℂ)*
      star (z (u+(i.val+1)))*z (u+(k.val+1)) else 0

noncomputable def countingTermRow (F : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (d : Fin 4 →₀ ℕ) (m B T H M u : ℕ) (c : ℕ → ℝ) (D : ℕ) (σ : ℝ)
    (z : ℕ → ℂ) (i : Fin M) (a b : Fin m) : ℂ :=
  ∑ j ∈ range (T+1),
    ((cutLagWeight H (min T (M-i.val)) (fun k =>
      countingTermCoefficient P d m B k c D T σ a b/(k : ℝ)) j : ℝ) : ℂ)*(F j : ℂ)*
    (z (u+(i.val+1)+j)*
      (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B a) (u+(i.val+1)+j) : ℂ))

theorem countingForwardRow_lag (F : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M u : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (z : ℕ → ℂ) (i : Fin M) :
    countingForwardRow F P m B L T H M u τ C c D σ z i =
      ∑ j ∈ range (T+1), if H < j ∧ j < min T (M-i.val) then
        (countingCandidateWithSeries F P m B L j τ C c D T σ
          (coefficientPrimeSet B (u+(i.val+1)))
          (coefficientPrimeSet B (u+(i.val+1)+j)) : ℂ)*
          star (z (u+(i.val+1)))*z (u+(i.val+1)+j) else 0 := by
  rw [← sum_fin_forward_lags i H T]
  unfold countingForwardRow
  apply sum_congr rfl
  intro k _
  by_cases hik : i < k
  · have hn : u+(i.val+1)+(k.val-i.val) = u+(k.val+1) := by
      have hh : i.val < k.val := hik
      omega
    simp only [ite_eq_left hik,countingSiteWithSeries,hn]
    by_cases hj : H < k.val-i.val ∧ k.val-i.val < T
    · simp [hik,hj.1,hj.2]
    · simp [hj]
  · simp [hik]

theorem countingForwardRow_features (F : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M u : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (z : ℕ → ℂ) (i : Fin M) :
    countingForwardRow F P m B L T H M u τ C c D σ z i =
      (independentRootMean B L τ C : ℂ)*
        ∑ d ∈ P.support, ∑ a, ∑ b,
          ((primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m d) B b)
            (u+(i.val+1)) : ℝ) : ℂ)*star (z (u+(i.val+1)))*
            countingTermRow F P d (m d) B T H M u (c d) (D d) σ z i a b := by
  rw [countingForwardRow_lag]
  have hpoint (j : ℕ) :
      (if H < j ∧ j < min T (M-i.val) then
        (countingCandidateWithSeries F P m B L j τ C c D T σ
          (coefficientPrimeSet B (u+(i.val+1)))
          (coefficientPrimeSet B (u+(i.val+1)+j)) : ℂ)*
          star (z (u+(i.val+1)))*z (u+(i.val+1)+j) else 0) =
      (independentRootMean B L τ C : ℂ)*
        ∑ d ∈ P.support, ∑ a, ∑ b,
          ((primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m d) B b)
            (u+(i.val+1)) : ℝ) : ℂ)*star (z (u+(i.val+1)))*
          (((cutLagWeight H (min T (M-i.val)) (fun k =>
            countingTermCoefficient P d (m d) B k (c d) (D d) T σ a b/(k : ℝ)) j : ℝ) : ℂ)*
            (F j : ℂ)*(z (u+(i.val+1)+j)*
              (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m d) B a)
                (u+(i.val+1)+j) : ℂ))) := by
    by_cases hj : H < j ∧ j < min T (M-i.val)
    · rw [ite_eq_left hj,countingCandidateWithSeries_arithmetic F P m B L j τ C c D T σ
        (by omega) (by omega)]
      simp only [cutLagWeight,ite_eq_left hj]
      push_cast
      simp only [mul_sum,sum_mul]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      ring
    · simp only [cutLagWeight,ite_eq_right hj,Complex.ofReal_zero,zero_mul,mul_zero,sum_const_zero]
  simp_rw [hpoint]
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  rw [← mul_sum]
  rfl

end JointDickman

end OAI
