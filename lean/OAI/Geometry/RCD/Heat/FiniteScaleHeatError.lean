import OAI.Geometry.RCD.Sobolev.FiniteScaleCutoffBudget

namespace OAI

/-! # Heat error from a finite normalization range and a Gaussian tail -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) [μ.Regular]
  {k : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ k)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)

include hk hχ hsχ in
/-- Finite-scale errors and the raw tail bound integrate with the same
Gaussian series. The radius cancels exactly against the kernel volume. -/
theorem finite_scale_heat_direction_error (u : SobolevSpace μ hQ) (c : ℝ)
    (n N : ℕ) (p : X) {r C V D B F b ε : ℝ} (hr : 0 < r)
    (hC : 0 ≤ C) (hV : 0 < V) (hD : 0 < D) (hF : 0 ≤ F) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (hχrange : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hupper : ∀ y, k (r ^ 2) p y ≤ (C / μ.real (ball y r)) *
      Real.exp (-(dist p y) ^ 2 / (D * r ^ 2) + B * r ^ 2))
    (hvol : ∀ y, χ y ≠ 0 → V * r ^ n ≤ μ.real (ball y r))
    (hbudget : ∀ j, (∫ y in ball p (2 ^ j * r), χ y * |localGamma μ hQ u u y - c| ∂μ) ≤
      F * r ^ n * splitSeriesTerm (fun i => b ^ i) ε N j) :
    (∫ y, (χ y * k (r ^ 2) p y) * |localGamma μ hQ u u y - c| ∂μ) ≤
      (F * C / V) * Real.exp (B * r ^ 2) *
        (ε * (∑' j, b ^ j * gaussianShellFactor D⁻¹ j) +
          ∑' j, b ^ (j + N) * gaussianShellFactor D⁻¹ (j + N)) := by
  let a := fun j => b ^ j * gaussianShellFactor D⁻¹ j
  have ha : Summable a := summable_gaussianShellFactor hb (inv_pos.mpr hD)
  have hapos (j : ℕ) : 0 ≤ a j := mul_nonneg (pow_nonneg hb _) (gaussianShellFactor_nonneg _ _)
  have heq (j : ℕ) : gaussianShellFactor D⁻¹ j *
      (F * r ^ n * splitSeriesTerm (fun i => b ^ i) ε N j) =
        (F * r ^ n) * splitSeriesTerm a ε N j := by
    dsimp [splitSeriesTerm, a]
    split_ifs <;> ring
  have hsum : Summable (fun j => gaussianShellFactor D⁻¹ j *
      (F * r ^ n * splitSeriesTerm (fun i => b ^ i) ε N j)) :=
    ((summable_splitSeriesTerm ha ε N).mul_left (F * r ^ n)).congr (fun j => (heq j).symm)
  have hheat := cutoff_heat_direction_error_le_series μ hQ hk hχ hsχ u c n p
    hr hC hV hD hχrange hupper hvol hbudget hsum
  have hsumEq : (∑' j, gaussianShellFactor D⁻¹ j *
      (F * r ^ n * splitSeriesTerm (fun i => b ^ i) ε N j)) =
        (F * r ^ n) * ∑' j, splitSeriesTerm a ε N j := by
    simp only [heq, tsum_mul_left]
  rw [hsumEq] at hheat
  have hcoeff : 0 ≤ ((C / (V * r ^ n)) * Real.exp (B * r ^ 2)) * (F * r ^ n) := by positivity
  have hsumBound := mul_le_mul_of_nonneg_left (tsum_splitSeriesTerm_le ha hapos hε N) hcoeff
  have hcancel : ((C / (V * r ^ n)) * Real.exp (B * r ^ 2)) * (F * r ^ n) =
      (F * C / V) * Real.exp (B * r ^ 2) := by
    field_simp [ne_of_gt hV, ne_of_gt hr]
  calc
    _ ≤ _ := hheat
    _ = (((C / (V * r ^ n)) * Real.exp (B * r ^ 2)) * (F * r ^ n)) *
        (∑' j, splitSeriesTerm a ε N j) := by ring
    _ ≤ _ := hsumBound
    _ = _ := by rw [hcancel]

end RegularPointCoordinates

end

end OAI
