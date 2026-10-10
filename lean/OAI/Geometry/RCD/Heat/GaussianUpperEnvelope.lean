import OAI.Geometry.RCD.Heat.GaussianHeatInput

namespace OAI

/-! # Coarse Gaussian envelopes needed for short heat differences -/

open Set MeasureTheory Metric

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) {ker : ℝ → X → X → ℝ}

/-- Fix one sufficient Gaussian denominator for the application. -/
theorem HasGaussianHeatBounds.upper_five (hg : HasGaussianHeatBounds μ ker) :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ t, 0 < t → ∀ x y,
      ker t x y ≤ C/μ.real (ball y (Real.sqrt t))*
        Real.exp (-dist x y^2/(5*t)+B*t) := by
  obtain ⟨C,B,hC,hB,h⟩ := hg (1/2) (by norm_num) (by norm_num)
  refine ⟨C,B,hC,hB,?_⟩
  intro t ht x y
  apply (h t ht x y).2.trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hC.le ENNReal.toReal_nonneg)
  apply Real.exp_le_exp.mpr
  have hpos : dist x y^2/(5*t) ≤ dist x y^2/((4+(1/2:ℝ))*t) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _)
    · positivity
    · nlinarith
  have hd : -dist x y^2/((4+(1/2:ℝ))*t) ≤ -dist x y^2/(5*t) := by
    simpa only [neg_div] using neg_le_neg hpos
  linarith

omit [MeasurableSpace X] in
/-- On a ball of twice the heat length, a Gaussian is bounded by a
Gaussian at its center with a coarser denominator. -/
theorem gaussian_upper_local {t C B V : ℝ} (ht : 0 < t) (hC : 0 ≤ C) (hV : 0 < V)
    (x z y : X) (hxy : dist x y ≤ 2*Real.sqrt t) :
    C/V*Real.exp (-dist y z^2/(5*t)+B*t) ≤
      C*Real.exp 1/V*Real.exp (-dist x z^2/(10*t)+B*t) := by
  have htS := Real.sq_sqrt ht.le
  have hd := dist_triangle x y z
  have hd2 : dist x z^2 ≤ 2*dist y z^2+8*t := by
    have hsum : dist x z ≤ 2*Real.sqrt t+dist y z := hd.trans (by linarith)
    have hsq := pow_le_pow_left₀ dist_nonneg hsum 2
    nlinarith [sq_nonneg (2*Real.sqrt t-dist y z)]
  have hexp : -dist y z^2/(5*t)+B*t ≤ 1+(-dist x z^2/(10*t)+B*t) := by
    field_simp
    nlinarith
  calc
    _ ≤ C/V*Real.exp (1+(-dist x z^2/(10*t)+B*t)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (div_nonneg hC hV.le)
    _ = _ := by rw [Real.exp_add]; ring

end RegularPointCoordinates

end

end OAI
