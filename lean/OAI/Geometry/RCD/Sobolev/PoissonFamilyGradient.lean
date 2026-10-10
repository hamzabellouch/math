import OAI.Geometry.RCD.Sobolev.PoissonCommonRegion

namespace OAI

/-! # Uniform interior gradient bounds for the actual Poisson family -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A single gradient constant works for every center and actual replacement,
including interior balls centered near the source center. -/
theorem poisson_family_gradient {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (hgradient : LocalPoissonGradientInput hX) {κ B : ℝ} (hκ : 0 ≤ κ) :
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∃ A : ℝ, 0 < A ∧ ∀ (p z : X) (r0 J Cχ : ℝ)
      (S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0)
      (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J Cχ) (i : ℕ),
      distanceSourceRadius r0 i ≤ 1 →
      dist z p ≤ distanceSourceRadius r0 i / 4 →
      -1 ≤ K * (distanceSourceRadius r0 i / 16) ^ 2 →
      ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
        localGamma (hausdorff n X) hX.quadratic (T.replacement i) (T.replacement i) x ≤
          (A * distanceSourceRadius r0 i) ^ 2 := by
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨C, hC, hbound⟩ := hgradient hn
  let G := 16 * max 8 B + ((n : ℝ) + 16 * κ) / 16
  have hG : 0 < G := by
    have hh := le_max_left (8 : ℝ) B
    dsimp only [G]
    positivity
  refine ⟨C * G, mul_pos (by linarith) hG, ?_⟩
  intro p z r0 J Cχ S T i hs1 hdist hcurv
  let s := distanceSourceRadius r0 i
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  have hsub : 8 * (s / 16) + dist z p ≤ s := by change dist z p ≤ s / 4 at hdist; linarith
  have hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball z (8 * (s / 16)))
      (T.replacement i) ((n : ℝ) + κ * (4 * s) ^ 2) :=
    T.laplacian_on_ball (hausdorff n X) hX.quadratic i z hsub
  have hv : ∀ᵐ x ∂(hausdorff n X).restrict (ball z (8 * (s / 16))),
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic (T.replacement i) x| ≤ max 8 B * s ^ 2 :=
    ae_restrict_of_ae (T.value_bound (hausdorff n X) hX.quadratic i)
  have hh := hbound z (s / 16) (by positivity) hcurv (T.replacement i)
    ((n : ℝ) + κ * (4 * s) ^ 2) (max 8 B * s ^ 2)
    (mul_nonneg ((by norm_num : (0 : ℝ) ≤ 8).trans (le_max_left _ _)) (sq_nonneg s)) hf hv
  have ha0 : 0 ≤ (n : ℝ) + κ * (4 * s) ^ 2 := by positivity
  have ha : (n : ℝ) + κ * (4 * s) ^ 2 ≤ (n : ℝ) + 16 * κ := by
    have hs2 : s ^ 2 ≤ 1 := by change s ≤ 1 at hs1; nlinarith
    have hm := mul_le_mul_of_nonneg_left hs2 hκ
    nlinarith
  have hraw : max 8 B * s ^ 2 / (s / 16) +
      |(n : ℝ) + κ * (4 * s) ^ 2| * (s / 16) ≤ G * s := by
    rw [abs_of_nonneg ha0]
    have he : max 8 B * s ^ 2 / (s / 16) = 16 * max 8 B * s := by field_simp
    rw [he]
    dsimp only [G]
    have hm := mul_le_mul_of_nonneg_right ha (by positivity : 0 ≤ s / 16)
    nlinarith
  have hraw0 : 0 ≤ C * (max 8 B * s ^ 2 / (s / 16) +
      |(n : ℝ) + κ * (4 * s) ^ 2| * (s / 16)) := by
    have hm : 0 ≤ max (8 : ℝ) B := (by norm_num : (0 : ℝ) ≤ 8).trans (le_max_left _ _)
    positivity
  have hcomp : (C * (max 8 B * s ^ 2 / (s / 16) +
      |(n : ℝ) + κ * (4 * s) ^ 2| * (s / 16))) ^ 2 ≤ ((C * G) * s) ^ 2 := by
    apply (sq_le_sq₀ hraw0 (mul_nonneg (mul_pos (by linarith) hG).le hs.le)).mpr
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hraw (by linarith : 0 ≤ C)
  rw [show 4 * (s / 16) = s / 4 by ring] at hh
  exact hh.mono fun _ hx => hx.trans hcomp

end RegularPointCoordinates

end

end OAI
