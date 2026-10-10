import OAI.Geometry.RCD.Heat.GaussianHeatInput

namespace OAI

/-! # The heat bounds actually used by the coordinate construction

Jiang--Li--Zhang (2016), Theorem 1.2, implies these bounds. The lower
estimate is needed only when squared distance is a fixed multiple of
time, and only for times at most one. The full two-sided
Gaussian estimate gives these local comparisons.
-/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

structure HasCoordinateHeatBounds (μ : Measure X) (k : ℝ → X → X → ℝ) : Prop where
  estimates : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧
    ∀ t : ℝ, 0 < t → ∀ x y : X, 0 ≤ k t x y ∧
      k t x y ≤ C/μ.real (ball y (Real.sqrt t))*Real.exp (-(dist x y)^2/((4+ε)*t)+B*t)
  localLower : ∀ A : ℝ, 0 ≤ A → ∃ c : ℝ, 0 < c ∧
    ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x y : X, (dist x y)^2 ≤ A*t →
      c/μ.real (ball y (Real.sqrt t)) ≤ k t x y

instance {μ : Measure X} {k : ℝ → X → X → ℝ} :
    CoeFun (HasCoordinateHeatBounds μ k) (fun _ => ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ t : ℝ, 0 < t → ∀ x y : X, 0 ≤ k t x y ∧
        k t x y ≤ C/μ.real (ball y (Real.sqrt t))*Real.exp (-(dist x y)^2/((4+ε)*t)+B*t)) :=
  ⟨HasCoordinateHeatBounds.estimates⟩

theorem HasGaussianHeatBounds.toCoordinate {μ : Measure X} {k : ℝ → X → X → ℝ}
    (hg : HasGaussianHeatBounds μ k) : HasCoordinateHeatBounds μ k where
  estimates ε hε hε1 := by
    obtain ⟨C,B,hC,hB,h⟩ := hg ε hε hε1
    exact ⟨C,B,hC,hB,fun t ht x y => ⟨le_trans (by positivity) (h t ht x y).1,(h t ht x y).2⟩⟩
  localLower A _hA := by
    obtain ⟨C,B,hC,hB,h⟩ := hg (1/2) (by norm_num) (by norm_num)
    let c := C⁻¹*Real.exp (-A/(4-1/2)-B)
    refine ⟨c,by dsimp only [c]; positivity,?_⟩
    intro t ht ht1 x y hd
    have hfrac : (dist x y)^2/((4-(1/2:ℝ))*t) ≤ A/(4-1/2) := by
      calc
        _ ≤ (A*t)/((4-(1/2:ℝ))*t) := div_le_div_of_nonneg_right hd (by positivity)
        _ = _ := by field_simp
    have hexp : -A/(4-(1/2:ℝ))-B ≤ -(dist x y)^2/((4-(1/2:ℝ))*t)-B*t := by
      have hb := mul_le_mul_of_nonneg_left ht1 hB
      have hh : -A/(4-(1/2:ℝ)) ≤ -(dist x y)^2/((4-(1/2:ℝ))*t) := by
        simpa only [neg_div] using neg_le_neg hfrac
      linarith only [hh,hb]
    calc
      _ = (C*μ.real (ball y (Real.sqrt t)))⁻¹*Real.exp (-A/(4-(1/2:ℝ))-B) := by
        dsimp only [c]
        rw [mul_inv_rev]
        ring
      _ ≤ (C*μ.real (ball y (Real.sqrt t)))⁻¹*
          Real.exp (-(dist x y)^2/((4-(1/2:ℝ))*t)-B*t) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
      _ ≤ _ := (h t ht x y).1

theorem HasCoordinateHeatBounds.upper_five (μ : Measure X) {k : ℝ → X → X → ℝ}
    (hg : HasCoordinateHeatBounds μ k) :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ t, 0 < t → ∀ x y,
      k t x y ≤ C/μ.real (ball y (Real.sqrt t))*Real.exp (-(dist x y)^2/(5*t)+B*t) := by
  obtain ⟨C,B,hC,hB,h⟩ := hg (1/2) (by norm_num) (by norm_num)
  refine ⟨C,B,hC,hB,?_⟩
  intro t ht x y
  apply (h t ht x y).2.trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hC.le ENNReal.toReal_nonneg)
  apply Real.exp_le_exp.mpr
  have hd : (dist x y)^2/(5*t) ≤ (dist x y)^2/((4+(1/2:ℝ))*t) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  have hh := neg_le_neg hd
  simpa only [neg_div] using add_le_add_left hh (B*t)

end RegularPointCoordinates

end

end OAI
