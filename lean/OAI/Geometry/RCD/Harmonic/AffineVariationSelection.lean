import OAI.Geometry.RCD.Coordinates.VanishingRadiusCost
import Mathlib.MeasureTheory.Integral.Average

namespace OAI

/-! # Joint selection of a small affine error and controlled coefficient variation -/

open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

private theorem affine_variation_product_bound {a v δ c : ℝ}
    (hv : 0≤v) (hδ : 0≤δ) (hδ1 : δ≤1) (ha : a≤δ*c) (hb : δ*v^2≤c) :
    a*v≤(c^2+c)/2 := by
  have h₁ : 2*(a*v)≤2*(δ*c*v) := by nlinarith [mul_le_mul_of_nonneg_right ha hv]
  have h₂ : 2*(δ*c*v)≤δ*c^2+δ*v^2 := by nlinarith [mul_nonneg hδ (sq_nonneg (c-v))]
  have h₃ : δ*c^2≤c^2 := mul_le_of_le_one_left (sq_nonneg c) hδ1
  linarith

theorem affine_variation_selection {Y : Type*} [MeasurableSpace Y]
    (μ : ℕ → Measure Y) [∀ k, IsProbabilityMeasure (μ k)]
    (A B E : ℕ → Y → ℝ) (P : ℕ → Y → Prop)
    (hA : ∀ k, Integrable (A k) (μ k)) (hB : ∀ k, Integrable (B k) (μ k))
    (hE : ∀ k, Integrable (E k) (μ k))
    (hA0 : ∀ k y, 0≤A k y) (hB0 : ∀ k y, 0≤B k y) (hE0 : ∀ k y, 0≤E k y)
    (hP : ∀ k, ∀ᵐ y ∂μ k, P k y)
    (hAlim : Tendsto (fun k => ∫ y, A k y ∂μ k) atTop (𝓝 0))
    (hElim : Tendsto (fun k => ∫ y, E k y ∂μ k) atTop (𝓝 0))
    {M : ℝ} (hM : ∀ k, (∫ y, B k y ∂μ k)≤M) :
    ∃ y : ℕ → Y, (∀ k, P k (y k)) ∧
      Tendsto (fun k => A k (y k)) atTop (𝓝 0) ∧
      Tendsto (fun k => E k (y k)) atTop (𝓝 0) ∧
      Tendsto (fun k => A k (y k)*Real.sqrt (B k (y k))) atTop (𝓝 0) := by
  obtain ⟨δ,hδ,hδ0,hδA⟩ := exists_vanishing_radius_cost
    (fun k => ∫ y, A k y ∂μ k) (fun k => integral_nonneg (hA0 k)) hAlim 1
  simp only [pow_one] at hδA
  have hδB : Tendsto (fun k => δ k*(∫ y, B k y ∂μ k)) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => mul_nonneg (hδ k).1.le (integral_nonneg (hB0 k)))
      (fun k => mul_le_mul_of_nonneg_left (hM k) (hδ k).1.le)
    simpa only [zero_mul] using hδ0.mul_const M
  let F k y := A k y/δ k+δ k*B k y+E k y
  have hFI (k : ℕ) : Integrable (F k) (μ k) :=
    (((hA k).div_const (δ k)).add ((hB k).const_mul (δ k))).add (hE k)
  have hF0 (k : ℕ) (y : Y) : 0≤F k y :=
    add_nonneg (add_nonneg (div_nonneg (hA0 k y) (hδ k).1.le)
      (mul_nonneg (hδ k).1.le (hB0 k y))) (hE0 k y)
  let c k := ∫ y, F k y ∂μ k
  have hc0 (k : ℕ) : 0≤c k := integral_nonneg (hF0 k)
  have hclim : Tendsto c atTop (𝓝 0) := by
    have hh := (hδA.add hδB).add hElim
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [] with k
    dsimp only [c,F]
    symm
    calc
      _ = (∫ y, A k y/δ k+δ k*B k y ∂μ k)+(∫ y, E k y ∂μ k) := by
        simpa only [Pi.add_apply] using
          integral_add (((hA k).div_const (δ k)).add ((hB k).const_mul (δ k))) (hE k)
      _ = _ := by
        congr 1
        calc
          _ = (∫ y, A k y/δ k ∂μ k)+(∫ y, δ k*B k y ∂μ k) := by
            simpa only [Pi.add_apply] using integral_add ((hA k).div_const (δ k)) ((hB k).const_mul (δ k))
          _ = _ := by rw [integral_div,integral_const_mul]
  have hex (k : ℕ) : ∃ y, P k y ∧ F k y≤c k := by
    obtain ⟨y,hy,hb⟩ := exists_notMem_null_le_integral (hFI k) (ae_iff.mp (hP k))
    exact ⟨y,of_not_not hy,hb⟩
  choose y hPy hy using hex
  have hAy (k : ℕ) : A k (y k)≤δ k*c k := by
    rw [mul_comm (δ k)]
    apply (div_le_iff₀ (hδ k).1).mp
    have hh := hy k
    dsimp only [F] at hh
    nlinarith [mul_nonneg (hδ k).1.le (hB0 k (y k)),hE0 k (y k)]
  have hBy (k : ℕ) : δ k*B k (y k)≤c k := by
    have hh := hy k
    dsimp only [F] at hh
    linarith [div_nonneg (hA0 k (y k)) (hδ k).1.le,hE0 k (y k)]
  have hEy (k : ℕ) : E k (y k)≤c k := by
    have hh := hy k
    dsimp only [F] at hh
    linarith [div_nonneg (hA0 k (y k)) (hδ k).1.le,mul_nonneg (hδ k).1.le (hB0 k (y k))]
  refine ⟨y,hPy,?_,squeeze_zero (fun k => hE0 k (y k)) hEy hclim,?_⟩
  · apply squeeze_zero (fun k => hA0 k (y k)) (fun k => (hAy k).trans ?_) hclim
    exact mul_le_of_le_one_left (hc0 k) (by linarith [(hδ k).2])
  · apply squeeze_zero (fun k => mul_nonneg (hA0 k (y k)) (Real.sqrt_nonneg _))
      (g := fun k => ((c k)^2+c k)/2)
    · intro k
      apply affine_variation_product_bound (Real.sqrt_nonneg _) (hδ k).1.le
        (by linarith [(hδ k).2]) (hAy k)
      simpa only [Real.sq_sqrt (hB0 k (y k))] using hBy k
    · simpa only [zero_pow (by decide : (2:ℕ)≠0),add_zero,zero_div] using
        ((hclim.pow 2).add hclim).div_const 2

end RegularPointCoordinates

end

end OAI
