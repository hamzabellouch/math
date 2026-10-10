import OAI.Geometry.RCD.Sobolev.ActualPoissonCommutatorSpan
import OAI.Geometry.RCD.Sobolev.ActualPoissonDifference
import OAI.Geometry.RCD.Sobolev.PoissonSpanLift
import OAI.Geometry.RCD.Sobolev.CorrectionInteriorEnergy

namespace OAI

/-! # The two-center commutator with the actual Poisson source budget -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual commutator error is linear in the two full source budgets,
including the curvature remainder, for every coordinate covector. -/
theorem actual_poisson_commutator_error {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianActionInput hX)
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
    ∀ b : Euclidean n, ∃ g h : SobolevSpace (hausdorff n X) hX.quadratic,
      let μ := hausdorff n X
      let s := distanceSourceRadius r0 i
      let Ω := ball z (s / 64)
      let v := T₂.replacement i - T₁.replacement i
      let a := sobolevColumnMap μ hX.quadratic u b
      (SobolevSpace.toLp μ hX.quadratic g =ᵐ[μ.restrict Ω] localGamma μ hX.quadratic (T₂.replacement i) a) ∧
      (SobolevSpace.toLp μ hX.quadratic h =ᵐ[μ.restrict Ω] localGamma μ hX.quadratic v a) ∧
      (∫ x in Ω, (localGamma μ hX.quadratic v g x -
        localGamma μ hX.quadratic (T₂.replacement i) h x - localGamma μ hX.quadratic v a x) ^ 2 ∂μ) ≤
        12 * A ^ 2 * s ^ 2 * ((n : ℝ) * (1 + epsilon)) ^ 2 * ‖b‖ ^ 2 *
          (4096 * Cχ * (J + B / 2) *
            ((S₁.source i).real (ball p₁ s) + (S₂.source i).real (ball p₂ s)) +
            κ * A ^ 2 * s ^ 2 * (μ.real (ball p₁ s) + μ.real (ball p₂ s))) := by
  dsimp only
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := distanceSourceRadius r0 i
  have hs : 0 < s := distanceSourceRadius_pos S₁.radius_pos i
  obtain ⟨L, _, M, henergy, hshift, hpair⟩ := actual_poisson_commutator_span hX hhessian
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
  intro b
  let a := poissonCoordinateLift b
  have ha : U a = sobolevColumnMap μ hQ u b := poissonSpanMap_lift μ hQ u f b
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
  have hga : ∀ᵐ x ∂μ.restrict (ball z (s / 64)),
      localGamma μ hQ (U a) (U a) x ≤ (((n : ℝ) * (1 + epsilon)) * ‖b‖) ^ 2 := by
    rw [ha]
    have hb := gamma_column_le_of_diagonal_bounds μ hQ u _ (1 + epsilon) hgrad b
    have ht := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith : s / 64 ≤ s / 4)) hb
    simpa only [mul_pow] using ht
  have he := hG v₂ (v₂ - v₁) a (A * s) (2 * A * s) (((n : ℝ) * (1 + epsilon)) * ‖b‖)
    (by positivity) (by positivity) (by positivity) hfg hvgrad hga
  have hbound : (∫ x in ball z (s / 64),
      (localGamma μ hQ (U (v₂ - v₁)) (G v₂ a).mixed x -
        localGamma μ hQ (U v₂) (G (v₂ - v₁) a).mixed x -
        localGamma μ hQ (U (v₂ - v₁)) (U a) x) ^ 2 ∂μ) ≤
      12 * A ^ 2 * s ^ 2 * ((n : ℝ) * (1 + epsilon)) ^ 2 * ‖b‖ ^ 2 * (Q₁ + Q₂) := by
    have h₁ := mul_le_mul_of_nonneg_left hmass'
      (show 0 ≤ (2 * A * s) ^ 2 * (((n : ℝ) * (1 + epsilon)) * ‖b‖) ^ 2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hdiff
      (show 0 ≤ (A * s) ^ 2 * (((n : ℝ) * (1 + epsilon)) * ‖b‖) ^ 2 by positivity)
    have h₃ := mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left hQ₁ : Q₂ ≤ Q₁ + Q₂)
      (show 0 ≤ A ^ 2 * s ^ 2 * ((n : ℝ) * (1 + epsilon)) ^ 2 * ‖b‖ ^ 2 by positivity)
    nlinarith only [he, h₁, h₂, h₃]
  have hresult : ∃ g h : SobolevSpace μ hQ,
      (SobolevSpace.toLp μ hQ g =ᵐ[μ.restrict (ball z (s / 64))] localGamma μ hQ (U v₂) (U a)) ∧
      (SobolevSpace.toLp μ hQ h =ᵐ[μ.restrict (ball z (s / 64))] localGamma μ hQ (U (v₂ - v₁)) (U a)) ∧
      (∫ x in ball z (s / 64), (localGamma μ hQ (U (v₂ - v₁)) g x -
        localGamma μ hQ (U v₂) h x - localGamma μ hQ (U (v₂ - v₁)) (U a) x) ^ 2 ∂μ) ≤
        12 * A ^ 2 * s ^ 2 * ((n : ℝ) * (1 + epsilon)) ^ 2 * ‖b‖ ^ 2 * (Q₁ + Q₂) :=
    ⟨(G v₂ a).mixed, (G (v₂ - v₁) a).mixed, (G v₂ a).mixed_rep,
      (G (v₂ - v₁) a).mixed_rep, hbound⟩
  rw [hv₂, hvdiff, ha] at hresult
  obtain ⟨g, h, hg, hh, hb⟩ := hresult
  refine ⟨g, h, hg, hh, ?_⟩
  have hsum : Q₁ + Q₂ =
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
