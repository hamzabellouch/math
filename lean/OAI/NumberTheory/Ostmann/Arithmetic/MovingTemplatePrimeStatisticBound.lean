import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplatePrimeStatistic

namespace OAI

/-! # The final full-cell statistic is controlled by its literal masked energy -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplatePrimeStatistic_full_cell_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφnorm : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ)
    (hν : ∀ i q, 0 ≤ ν i q) (hmass : ∀ i, ∑ q, ν i q = 1)
    (hidentical : ∀ j k, ν (movingTemplateBulk n r m j) = ν (movingTemplateBulk n r m k))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (H : ℝ) :
    ‖movingTemplatePrimeStatistic P outside μ childBound pivotBound V F φ G n r m ν
      greg ggiant favorable H (H - 1) (H + 1) (H - 1) (H + 1)‖ ^ 2 ≤
    diagonalOuterMajorant Bφ Dφ false * (2 * V n + 1 : ℕ) * Real.exp 5 *
      ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
        n r m ν (fun _ => true) greg H H false (H - 1) (H + 1) (H - 1) (H + 1) H‖ := by
  let W := fun (_ : ℤ) (_ : MovingRegularSlot n r m → P) (x z : ℝ) =>
    giantOuterWeight φ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  have hC := (diagonalOuterMajorant_pos Bφ Dφ false).le
  have hW (s y x z) : 0 ≤ (W s y x z).re := by
    obtain ⟨a, ha, he⟩ := giantOuterWeight_positive φ hφ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
    change W s y x z = (a : ℂ) at he
    rw [he]
    exact ha
  have hWu (s y x z) : (W s y x z).re ≤ diagonalOuterMajorant Bφ Dφ false := by
    apply (Complex.re_le_norm _).trans
    exact (giantOuterWeight_norm φ H H Bφ Dφ hBφ hDφ hφnorm hlip hout false _ _).trans
      (by unfold diagonalOuterMajorant; linarith)
  have hm0 := mixedExternalAverage_re_nonneg ν hν (V n)
    (H - 1) (H + 1) (H - 1) (H + 1) H W hW
  have hmb := mixedExternalAverage_mass_bound ν hν hmass (V n)
    (H - 1) (H + 1) (H - 1) (H + 1) H (diagonalOuterMajorant Bφ Dφ false) hC W hWu
  have hmupper : (mixedExternalAverage ν (V n)
      (H - 1) (H + 1) (H - 1) (H + 1) H W).re ≤
      diagonalOuterMajorant Bφ Dφ false * (2 * V n + 1 : ℕ) * Real.exp 3 := by
    simpa only [show H + 1 - (H - 1) + (H + 1 - H) = 3 by ring] using hmb
  have hc := movingTemplatePrimeStatistic_cauchy P hP outside μ childBound pivotBound V F
    φ hφ G n r m ν hν hidentical greg ggiant favorable H
    (H - 1) (H + 1) (H - 1) (H + 1) H
  have he := Complex.re_le_norm (movingTemplateMaskedSymmetrizedEnergy P hP outside μ
    childBound pivotBound V F φ G n r m ν (fun _ => true) greg H H false
    (H - 1) (H + 1) (H - 1) (H + 1) H)
  have hstep := mul_le_mul_of_nonneg_left he (mul_nonneg (sq_nonneg (Real.exp (H - (H - 1)))) hm0)
  have hnext := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmupper (sq_nonneg (Real.exp (H - (H - 1)))))
    (norm_nonneg (movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F
      φ G n r m ν (fun _ => true) greg H H false (H - 1) (H + 1) (H - 1) (H + 1) H))
  apply hc.trans ((hstep.trans hnext).trans_eq ?_)
  rw [show H - (H - 1) = 1 by ring]
  have hExp : Real.exp 1 ^ 2 * Real.exp 3 = Real.exp 5 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    norm_num
  calc
    _ = (diagonalOuterMajorant Bφ Dφ false * (2 * V n + 1 : ℕ)) *
      (Real.exp 1 ^ 2 * Real.exp 3) *
      ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
        n r m ν (fun _ => true) greg H H false (H - 1) (H + 1) (H - 1) (H + 1) H‖ := by ring
    _ = _ := by rw [hExp]

end Ostmann

end OAI
