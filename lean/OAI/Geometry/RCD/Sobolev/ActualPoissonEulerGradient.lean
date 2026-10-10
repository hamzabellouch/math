import OAI.Geometry.RCD.Sobolev.ActualPoissonCommutatorSpan
import OAI.Geometry.RCD.Sobolev.ActualPoissonDifference
import OAI.Geometry.RCD.Sobolev.PoissonSpanLift
import OAI.Geometry.RCD.Sobolev.CorrectionInteriorEnergy
import OAI.Geometry.RCD.Sobolev.GradientProductInput

namespace OAI

/-! # The Euler-gradient error of the actual two-center Poisson difference -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The gradient of Gamma(f,v)-v is controlled by the two actual source
budgets, including the curvature remainder and all singular mass. -/
theorem actual_poisson_euler_gradient {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    {κ B J C A Cχ epsilon r0 : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hB : 0 ≤ B) (hJ : 0 ≤ J) (hCχ : 0 ≤ Cχ)
    (hA : 0 ≤ A) (hepsilon : 0 ≤ epsilon) (p₁ p₂ z : X)
    (S₁ : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p₁ r0)
    (S₂ : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p₂ r0)
    (T₁ : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S₁ B J C)
    (T₂ : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S₂ B J C)
    (i : ℕ)
    (hroom₁ : dist z p₁ ≤ distanceSourceRadius r0 i / 4)
    (hroom₂ : dist z p₂ ≤ distanceSourceRadius r0 i / 4)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball z (distanceSourceRadius r0 i / 4)) (u j))
    (hgrad : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ (1 + epsilon) ^ 2)
    (hf₁ : ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T₁.replacement i) (T₁.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (hf₂ : ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T₂.replacement i) (T₂.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic z (distanceSourceRadius r0 i / 64) Cχ) :
    ∃ g : SobolevSpace (hausdorff n X) hX.quadratic,
      let μ := hausdorff n X
      let s := distanceSourceRadius r0 i
      let Ω := ball z (s / 64)
      let v := T₂.replacement i - T₁.replacement i
      (SobolevSpace.toLp μ hX.quadratic g =ᵐ[μ.restrict Ω]
        localGamma μ hX.quadratic (T₂.replacement i) v) ∧
      (∫ x in Ω, localGamma μ hX.quadratic (g - v) (g - v) x ∂μ) ≤
        12 * A ^ 2 * s ^ 2 *
          (4096 * Cχ * (J + B / 2) *
            ((S₁.source i).real (ball p₁ s) + (S₂.source i).real (ball p₂ s)) +
            κ * A ^ 2 * s ^ 2 * (μ.real (ball p₁ s) + μ.real (ball p₂ s))) := by
  dsimp only
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := distanceSourceRadius r0 i
  have hs : 0 < s := distanceSourceRadius_pos S₁.radius_pos i
  obtain ⟨L, hL, M, henergy, hshift, hpair⟩ := actual_poisson_commutator_span hX hhessian
    hκ hK hA hepsilon p₁ p₂ z S₁ S₂ T₁ T₂ i hroom₁ hroom₂ u hu hgrad hf₁ hf₂
  let f : Fin 2 → SobolevSpace μ hQ := ![T₁.replacement i, T₂.replacement i]
  let U := sobolevColumnMap μ hQ (poissonSpan μ hQ u f)
  let ell := poissonSpanLaplacian n ((n : ℝ) + κ * (4 * s) ^ 2)
  let v₁ : Euclidean (n + 2) := EuclideanSpace.single (Fin.natAdd n (0 : Fin 2)) 1
  let v₂ : Euclidean (n + 2) := EuclideanSpace.single (Fin.natAdd n (1 : Fin 2)) 1
  have hv₁ : U v₁ = T₁.replacement i := poissonSpanMap_right μ hQ u f 0
  have hv₂ : U v₂ = T₂.replacement i := poissonSpanMap_right μ hQ u f 1
  have hell₁ : ell v₁ = (n : ℝ) + κ * (4 * s) ^ 2 := poissonSpanLaplacian_right _ 0
  have hell₂ : ell v₂ = (n : ℝ) + κ * (4 * s) ^ 2 := poissonSpanLaplacian_right _ 1
  have hvdiff : U (v₂ - v₁) = T₂.replacement i - T₁.replacement i := by rw [map_sub, hv₂, hv₁]
  let _ : IsFiniteMeasure (μ.restrict (ball z (2 * (s / 32)))) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
  obtain ⟨G₁⟩ := henergy v₁
  obtain ⟨G₂⟩ := henergy v₂
  have hfsmall₁ : ∀ᵐ x ∂μ.restrict (ball z (2 * (s / 32))),
      localGamma μ hQ (T₁.replacement i) (T₁.replacement i) x ≤ A ^ 2 * s ^ 2 := by
    have ht := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith : 2 * (s / 32) ≤ s / 4)) hf₁
    simpa only [mul_pow] using ht
  have hfsmall₂ : ∀ᵐ x ∂μ.restrict (ball z (2 * (s / 32))),
      localGamma μ hQ (T₂.replacement i) (T₂.replacement i) x ≤ A ^ 2 * s ^ 2 := by
    have ht := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith : 2 * (s / 32) ≤ s / 4)) hf₂
    simpa only [mul_pow] using ht
  let Q₁ := 4096 * Cχ * (J + B / 2) * (S₁.source i).real (ball p₁ s) + κ * A ^ 2 * s ^ 2 * μ.real (ball p₁ s)
  let Q₂ := 4096 * Cχ * (J + B / 2) * (S₂.source i).real (ball p₂ s) + κ * A ^ 2 * s ^ 2 * μ.real (ball p₂ s)
  have hQ₁ : 0 ≤ Q₁ := by dsimp only [Q₁]; positivity
  have hQ₂ : 0 ≤ Q₂ := by dsimp only [Q₂]; positivity
  have hmass := T₂.shifted_mass_le μ hQ i hκ hCχ hroom₂ ell G₂ hv₂ hell₂ hshift χ hfsmall₂
  have hmass' : (M.measure v₂).real (ball z (s / 64)) -
      (2 * ell v₂ - (n : ℝ)) * μ.real (ball z (s / 64)) ≤ Q₂ := by
    have hm := ShiftedBochnerMeasure.mass M (μ.restrict (ball z (2 * (s / 32))))
      ell (n : ℝ) hshift v₂ 1 (ball z (s / 64)) measurableSet_ball
    rw [measureReal_restrict_apply measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball (by linarith : s / 64 ≤ 2 * (s / 32)))] at hm
    simp only [one_pow, mul_one] at hm
    change ((shiftedBochnerMeasure M (μ.restrict (ball z (2 * (s / 32))))
      ell (n : ℝ) hshift).measure (WithLp.toLp 2 (v₂, (1 : ℝ)))).real (ball z (s / 64)) ≤ Q₂ at hmass
    rwa [hm] at hmass
  have hdiff : (M.measure (v₂ - v₁)).real (ball z (s / 64)) ≤ 2 * (Q₁ + Q₂) := by
    have hh := actual_poisson_difference_mass_le μ hQ T₁ T₂ i hκ hCχ hroom₁ hroom₂ ell
      G₁ G₂ hv₁ hv₂ hell₁ hell₂ hshift χ hfsmall₁ hfsmall₂
    convert hh using 1; dsimp only [Q₁, Q₂]; ring
  obtain ⟨G, hG⟩ := hpair (s / 64) (by positivity) (by linarith)
  have hfg : ∀ᵐ x ∂μ.restrict (ball z (s / 64)),
      localGamma μ hQ (U v₂) (U v₂) x ≤ (A * s) ^ 2 := by
    rw [hv₂]
    exact ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith : s / 64 ≤ s / 4)) hf₂
  have hvgrad : ∀ᵐ x ∂μ.restrict (ball z (s / 64)),
      localGamma μ hQ (U (v₂ - v₁)) (U (v₂ - v₁)) x ≤ (2 * A * s) ^ 2 := by
    rw [hvdiff]
    have hneg : localGamma μ hQ (-T₁.replacement i) (-T₁.replacement i) =ᵐ[μ]
        localGamma μ hQ (T₁.replacement i) (T₁.replacement i) := by
      filter_upwards [localGamma_smul_left μ hQ (-1) (T₁.replacement i) (-T₁.replacement i),
        localGamma_smul_right μ hQ (-1) (T₁.replacement i) (T₁.replacement i)] with x h₁ h₂
      simp only [neg_one_smul, neg_one_mul] at h₁ h₂
      exact h₁.trans ((congrArg Neg.neg h₂).trans (neg_neg _))
    have hb₁ := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith : s / 64 ≤ s / 4)) hf₁
    have hb₂ := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith : s / 64 ≤ s / 4)) hf₂
    have hsum := localGamma_add_self_le μ hQ (T₂.replacement i) (-T₁.replacement i)
    filter_upwards [hb₁, hb₂, ae_restrict_of_ae hneg,
      ae_restrict_of_ae hsum] with x h₁ h₂ hn hh
    rw [← sub_eq_add_neg, hn] at hh
    nlinarith only [h₁, h₂, hh]
  have hLap : ∀ q, IsConstantLaplacianOn μ hQ (ball z (8 * (s / 32))) (U q) (ell q) := by
    intro q
    rw [show 8 * (s / 32) = s / 4 by ring]
    apply poissonSpan_constant_laplacian μ hQ u f _ hu
    intro j
    fin_cases j
    · exact T₁.laplacian_on_ball μ hQ i z (by
        change s / 4 + dist z p₁ ≤ s
        change dist z p₁ ≤ s / 4 at hroom₁
        linarith)
    · exact T₂.laplacian_on_ball μ hQ i z (by
        change s / 4 + dist z p₂ ≤ s
        change dist z p₂ ≤ s / 4 at hroom₂
        linarith)
  have hfullgrad : ∀ q, ∀ᵐ x ∂μ.restrict (ball z (8 * (s / 32))),
      localGamma μ hQ (U q) (U q) x ≤ (L : ℝ) ^ 2 * ‖q‖ ^ 2 := by
    intro q
    rw [show 8 * (s / 32) = s / 4 by ring, hL]
    apply poissonSpan_gradient μ hQ u f (max (1 + epsilon) (A * s))
    · intro j
      filter_upwards [hgrad j] with x hx
      exact hx.trans ((sq_le_sq₀ (by linarith)
        ((by linarith : 0 ≤ 1 + epsilon).trans (le_max_left _ _))).mpr (le_max_left _ _))
    · intro j
      have hj : ∀ᵐ x ∂μ.restrict (ball z (s / 4)),
          localGamma μ hQ (f j) (f j) x ≤ (A * s) ^ 2 := by
        fin_cases j
        · exact hf₁
        · exact hf₂
      filter_upwards [hj] with x hx
      exact hx.trans ((sq_le_sq₀ (mul_nonneg hA hs.le)
        ((by linarith : 0 ≤ 1 + epsilon).trans (le_max_left _ _))).mpr (le_max_right _ _))
  let g := (G v₂ (v₂ - v₁)).mixed
  have he := hproduct κ hκ hK z (s / 32) (by positivity) L U ell hLap hfullgrad M henergy
    (s / 64) (by positivity) (by linarith) v₂ (v₂ - v₁) g (G v₂ (v₂ - v₁)).mixed_rep
    1 (A * s) (2 * A * s) (by positivity) (by positivity) hfg hvgrad
  simp only [one_smul, one_pow, mul_one] at he
  have h₁ := mul_le_mul_of_nonneg_left hmass' (show 0 ≤ 2 * (2 * A * s) ^ 2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hdiff (show 0 ≤ 2 * (A * s) ^ 2 by positivity)
  have h₃ := mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left hQ₁ : Q₂ ≤ Q₁ + Q₂) (show 0 ≤ 8 * A ^ 2 * s ^ 2 by positivity)
  have hb : (∫ x in ball z (s / 64), localGamma μ hQ (g - U (v₂ - v₁))
      (g - U (v₂ - v₁)) x ∂μ) ≤ 12 * A ^ 2 * s ^ 2 * (Q₁ + Q₂) := by
    nlinarith only [he, h₁, h₂, h₃]
  rw [hvdiff] at hb
  refine ⟨g, ?_, ?_⟩
  · have hg : SobolevSpace.toLp μ hQ g =ᵐ[μ.restrict (ball z (s / 64))]
        localGamma μ hQ (U v₂) (U (v₂ - v₁)) := (G v₂ (v₂ - v₁)).mixed_rep
    rwa [hv₂, hvdiff] at hg
  · have hsum : Q₁ + Q₂ =
        4096 * Cχ * (J + B / 2) *
          ((S₁.source i).real (ball p₁ s) + (S₂.source i).real (ball p₂ s)) +
          κ * A ^ 2 * s ^ 2 * (μ.real (ball p₁ s) + μ.real (ball p₂ s)) := by
      dsimp only [Q₁, Q₂]
      ring
    rw [hsum] at hb
    exact hb

end RegularPointCoordinates

end

end OAI
