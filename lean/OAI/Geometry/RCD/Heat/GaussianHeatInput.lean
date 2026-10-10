import OAI.Geometry.RCD.Heat.HeatGramComparison
import OAI.Geometry.RCD.Heat.ActualHeatMass

namespace OAI

/-!
# The quantitative published heat-kernel input

Jiang--Li--Zhang (2016), Theorem 1.2, gives these two Gaussian
bounds on `RCD*(K,N)` spaces for `K < 0`. We use only `0 < ε < 1`
and finite-dimensional noncollapsed spaces.
Source: https://arxiv.org/pdf/1407.5289v2 .
-/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (p : ℝ → X → X → ℝ)

/-- The pair of Gaussian bounds, with the measure at the kernel's second
argument and the exact `4 ± ε` denominators. -/
def HasGaussianHeatBounds : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 ≤ C₂ ∧
    ∀ t : ℝ, 0 < t → ∀ x y : X,
      (C₁ * μ.real (Metric.ball y (Real.sqrt t)))⁻¹ *
        Real.exp (-(dist x y) ^ 2 / ((4 - ε) * t) - C₂ * t) ≤ p t x y ∧
      p t x y ≤ (C₁ / μ.real (Metric.ball y (Real.sqrt t))) *
        Real.exp (-(dist x y) ^ 2 / ((4 + ε) * t) + C₂ * t)

/-- A Gaussian lower bound becomes uniform on any testing set where the
distance and local ball volumes have the stated uniform bounds. -/
theorem gaussian_lower_on_set {s : Set X} {t ε C₁ C₂ A V : ℝ}
    (ht : 0 < t) (hε : ε < 1) (hC : 0 < C₁)
    (x : X)
    (hlower : ∀ y ∈ s,
      (C₁ * μ.real (Metric.ball y (Real.sqrt t)))⁻¹ *
        Real.exp (-(dist x y) ^ 2 / ((4 - ε) * t) - C₂ * t) ≤ p t x y)
    (hvolume : ∀ y ∈ s, 0 < μ.real (Metric.ball y (Real.sqrt t)) ∧
      μ.real (Metric.ball y (Real.sqrt t)) ≤ V)
    (hdist : ∀ y ∈ s, (dist x y) ^ 2 ≤ A * t) :
    ∀ y ∈ s, (C₁ * V)⁻¹ * Real.exp (-A / (4 - ε) - C₂ * t) ≤ p t x y := by
  intro y hy
  have hden : 0 < 4 - ε := by linarith
  have hvol := hvolume y hy
  have hinv : (C₁ * V)⁻¹ ≤ (C₁ * μ.real (Metric.ball y (Real.sqrt t)))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (mul_pos hC hvol.1) (mul_le_mul_of_nonneg_left hvol.2 hC.le)
  have hfrac : (dist x y) ^ 2 / ((4 - ε) * t) ≤ A / (4 - ε) := by
    calc
      _ ≤ (A * t) / ((4 - ε) * t) :=
        div_le_div_of_nonneg_right (hdist y hy) (mul_pos hden ht).le
      _ = _ := by field_simp
  have hexp : Real.exp (-A / (4 - ε) - C₂ * t) ≤
      Real.exp (-(dist x y) ^ 2 / ((4 - ε) * t) - C₂ * t) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using sub_le_sub_right (neg_le_neg hfrac) (C₂ * t)
  exact (mul_le_mul hinv hexp (Real.exp_pos _).le
    (inv_nonneg.mpr (mul_pos hC hvol.1).le)).trans (hlower y hy)

variable [BorelSpace X] [ProperSpace X] [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The cited Gaussian estimate supplies the lower comparison for the
actual cutoff heat Gram on any fixed ball satisfying volume bounds.
The positive constant is chosen before the coefficient vector. -/
theorem HasGaussianHeatBounds.exists_heatGram_lower_mean
    (hg : HasGaussianHeatBounds μ p) (hp : IsContinuousHeatKernel μ hQ p)
    {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)
    (U : E →L[ℝ] SobolevSpace μ hQ) (s : Set X) (hs : MeasurableSet s)
    (hμ : 0 < μ.real s) (hχpos : ∀ y, 0 ≤ χ y) (hχone : ∀ y ∈ s, χ y = 1)
    {t : ℝ} (ht : 0 < t) (x : X) {V A lambda : ℝ} (hV : 0 < V)
    (hlambda : 0 ≤ lambda)
    (hvolume : ∀ y ∈ s, 0 < μ.real (Metric.ball y (Real.sqrt t)) ∧
      μ.real (Metric.ball y (Real.sqrt t)) ≤ V)
    (hdist : ∀ y ∈ s, (dist x y) ^ 2 ≤ A * t) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : E,
      c * ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ ≤
        ⟪v, cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda v⟫_ℝ := by
  obtain ⟨C₁, C₂, hC₁, _hC₂, hbounds⟩ := hg (1 / 2) (by norm_num) (by norm_num)
  let L := (C₁ * V)⁻¹ * Real.exp (-A / (4 - 1 / 2) - C₂ * t)
  have hL : 0 < L := mul_pos (inv_pos.mpr (mul_pos hC₁ hV)) (Real.exp_pos _)
  have hk : ∀ y ∈ s, L ≤ p t x y :=
    gaussian_lower_on_set μ p ht (by norm_num) hC₁ x
      (fun y _ => (hbounds t ht x y).1) hvolume hdist
  refine ⟨μ.real s * L, mul_pos hμ hL, fun v => ?_⟩
  apply cutoffHeatGram_lower_mean μ hQ hp hχ hsχ U s hs hχpos hχone ht x hlambda
  intro y hy
  convert hk y hy using 1
  field_simp [ne_of_gt hμ]

/-- One Gaussian constant controls both actual Gram energy and the full
local mass measure. This is the common lower bound used when heat decrements
are compared to normalized ball masses. -/
theorem HasGaussianHeatBounds.exists_heatGram_mass_lower
    [FiniteDimensional ℝ E]
    (hg : HasGaussianHeatBounds μ p) (hp : IsContinuousHeatKernel μ hQ p)
    {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)
    (U : E →L[ℝ] SobolevSpace μ hQ) (M : PositiveBilinearMeasure X E)
    (s : Set X) (hs : MeasurableSet s) (hμ : 0 < μ.real s)
    (hχpos : ∀ y, 0 ≤ χ y) (hχone : ∀ y ∈ s, χ y = 1)
    {t : ℝ} (ht : 0 < t) (x : X) {V A lambda : ℝ} (hV : 0 < V)
    (hlambda : 0 ≤ lambda)
    (hvolume : ∀ y ∈ s, 0 < μ.real (Metric.ball y (Real.sqrt t)) ∧
      μ.real (Metric.ball y (Real.sqrt t)) ≤ V)
    (hdist : ∀ y ∈ s, (dist x y) ^ 2 ≤ A * t) :
    ∃ L : ℝ, 0 < L ∧ ∀ v : E,
      (μ.real s * L) * ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ ≤
        ⟪v, cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda v⟫_ℝ ∧
      L * ⟪v, M.massOperator s v⟫_ℝ ≤
        ⟪v, cutoffHeatMass μ hQ hp hχ hsχ M ht x v⟫_ℝ := by
  obtain ⟨C₁, C₂, hC₁, _hC₂, hbounds⟩ := hg (1 / 2) (by norm_num) (by norm_num)
  let L := (C₁ * V)⁻¹ * Real.exp (-A / (4 - 1 / 2) - C₂ * t)
  have hL : 0 < L := mul_pos (inv_pos.mpr (mul_pos hC₁ hV)) (Real.exp_pos _)
  have hk : ∀ y ∈ s, L ≤ p t x y :=
    gaussian_lower_on_set μ p ht (by norm_num) hC₁ x
      (fun y _ => (hbounds t ht x y).1) hvolume hdist
  refine ⟨L, hL, fun v => ⟨?_, ?_⟩⟩
  · apply cutoffHeatGram_lower_mean μ hQ hp hχ hsχ U s hs hχpos hχone ht x hlambda
    intro y hy
    convert hk y hy using 1
    field_simp [ne_of_gt hμ]
  · exact cutoffHeatMass_lower_mass μ hQ hp hχ hsχ M hχpos ht x s hs hχone L hk v

end RegularPointCoordinates

end

end OAI
