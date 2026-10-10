import OAI.Geometry.RCD.Coordinates.RegularizedMonotoneHeat
import OAI.Geometry.RCD.Heat.GaussianHeatInput

namespace OAI

/-! # Actual heat increments control the full local Bochner mass -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

omit [BorelSpace X] [ProperSpace X] [μ.Regular] in
/-- One Gaussian lower constant works on the entire dyadic time block,
including when the reference measure has global negative-curvature growth. -/
theorem gaussian_lower_on_time_block (hg : HasGaussianHeatBounds μ ker)
    (n : ℕ) {r V A : ℝ} (hr : 0 < r) (hV : 0 < V) (hA : 0 ≤ A)
    (x : X) (S : Set X)
    (hvolume : ∀ t, r ^ 2 / 4 ≤ t → t ≤ r ^ 2 → ∀ y ∈ S,
      0 < μ.real (ball y (Real.sqrt t)) ∧
        μ.real (ball y (Real.sqrt t)) ≤ V * r ^ n)
    (hdist : ∀ y ∈ S, (dist x y) ^ 2 ≤ A * r ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, r ^ 2 / 4 ≤ t → t ≤ r ^ 2 → ∀ y ∈ S, c ≤ ker t x y := by
  obtain ⟨C, B, hC, hB, hgauss⟩ := hg (1 / 2) (by norm_num) (by norm_num)
  let c := (C * (V * r ^ n))⁻¹ * Real.exp (-(4 * A) / (4 - 1 / 2) - B * r ^ 2)
  have hc : 0 < c := mul_pos (inv_pos.mpr (mul_pos hC (mul_pos hV (pow_pos hr n))))
    (Real.exp_pos _)
  refine ⟨c, hc, fun t hlow hupp => ?_⟩
  have ht : 0 < t := (div_pos (sq_pos_of_pos hr) (by norm_num)).trans_le hlow
  have hl := gaussian_lower_on_set μ ker ht (by norm_num : (1 / 2 : ℝ) < 1) hC x
    (fun y _ => (hgauss t ht x y).1) (hvolume t hlow hupp)
    (A := 4 * A) (fun y hy => by
      have hm := mul_le_mul_of_nonneg_left hlow hA
      nlinarith [hdist y hy])
  intro y hy
  have he : c ≤ (C * (V * r ^ n))⁻¹ * Real.exp (-(4 * A) / (4 - 1 / 2) - B * t) := by
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hupp hB
    linarith
  exact he.trans (hl y hy)

variable {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean n)} {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ C : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C)

/-- Integrating the canonical lower heat derivative controls the full
Bochner mass on any set where the cutoff is one. No density for the mass
measure is required. -/
theorem harmonic_heat_increment_lower_mass (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    (S : Set X) (hS : MeasurableSet S) (hχone : ∀ y ∈ S, (χ.weight : X → ℝ) y = 1)
    {s t c η lambda : ℝ} (hs : 0 < s) (hst : s ≤ t) (hlambda0 : 0 ≤ lambda)
    (hlambda : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda)
    (herror : ∀ u ∈ Icc s t, ‖harmonicHeatError μ hQ (k := ker) G χ u p‖ ≤ η)
    (hkernel : ∀ u ∈ Icc s t, ∀ y ∈ S, c ≤ ker u p y)
    (v : Euclidean n) :
    (2 * c * (t - s)) * ⟪v, M.massOperator S v⟫_ℝ ≤
      ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
        U (hs.trans_le hst) p lambda v⟫_ℝ -
      ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
        U hs p lambda v⟫_ℝ := by
  let F := fun u => ⟪v, cutoffHeatGramAt μ hQ hk χ.weight.continuous
    (χ.hasCompactSupport μ hQ) U u p lambda v⟫_ℝ
  let b := 2 * c * ⟪v, M.massOperator S v⟫_ℝ
  have hderiv (u : ℝ) (hu : u ∈ Icc s t) :
      HasDerivAt F ⟪v, harmonicHeatDerivative μ hQ hk G χ (hs.trans_le hu.1) p lambda v⟫_ℝ u :=
    harmonicHeatQuadratic_hasDerivAt μ hQ hk G χ hρ hρr (hs.trans_le hu.1) p hlambda0 v
  have hbound (u : ℝ) (hu : u ∈ Icc s t) :
      b ≤ ⟪v, harmonicHeatDerivative μ hQ hk G χ (hs.trans_le hu.1) p lambda v⟫_ℝ := by
    have hm := cutoffHeatMass_lower_mass μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) M (fun y => (χ.bounds y).1) (hs.trans_le hu.1) p S hS hχone
      c (hkernel u hu) v
    have hd := (harmonicHeatDerivative_bounds μ hQ hk G χ hρr hκ (hs.trans_le hu.1) p
      (herror u hu) hlambda v).1
    dsimp only [b]
    linarith
  have hm := (convex_Icc s t).mul_sub_le_image_sub_of_le_deriv
    (fun u hu => (hderiv u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hderiv u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (C := b)
    (fun u hu => by
      rw [(hderiv u (interior_subset hu)).deriv]
      exact hbound u (interior_subset hu))
    s (left_mem_Icc.mpr hst) t (right_mem_Icc.mpr hst) hst
  dsimp only [F, b] at hm
  rw [cutoffHeatGramAt_of_pos μ hQ hk _ _ U hs,
    cutoffHeatGramAt_of_pos μ hQ hk _ _ U (hs.trans_le hst)] at hm
  linarith

end RegularPointCoordinates

end

end OAI
