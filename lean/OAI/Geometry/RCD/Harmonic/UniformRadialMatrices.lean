import OAI.Geometry.RCD.Sobolev.UniformRadialEnergy
import OAI.Geometry.RCD.Harmonic.UniformRadialCoefficient
import OAI.Geometry.RCD.Harmonic.DyadicRadialMatrices

namespace OAI

/-! # One set of constants for all actual radial matrices -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The matrix and residual estimates use constants chosen before the
root, center, coordinates and splitting error. -/
theorem dyadic_radial_matrices_uniform {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [IsFiniteMeasureOnCompacts (hausdorff (m + 2) X)]
    (hhessian : LocalPoissonHessianInput hX) (hmean : LocalHarmonicL2MeanValueInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    {B J A Cχ κ₀ : ℝ} {d : ℕ} (hB : 0 ≤ B) (hJ : 0 ≤ J) (hA : 0 ≤ A)
    (hCχ : 0 ≤ Cχ) (hκ₀ : 0 ≤ κ₀) (hd : 0 < d) :
    ∃ Cg D Ca : ℝ, 1 ≤ Cg ∧ 0 < D ∧ 1 ≤ Ca ∧ ∀ {a κ r0 C L δ ε : ℝ} {p : X},
    ∀ (_ha : 0 ≤ a) (_hκ : 0 ≤ κ) (_hK : -κ ≤ K)
    (_hr01 : r0 ≤ 1) (_hscale : a * (3 * r0) ≤ 1)
    (_hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (S : DyadicDistanceSources (hausdorff (m + 2) X) hX.quadratic (m + 2) κ p r0)
    (T : DyadicDistanceReplacements (hausdorff (m + 2) X) hX.quadratic S B J C)
    (_hP : Summable (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic S))
    (_hquarter : ∀ t : ℝ, 0 < t → t ≤ r0 →
      |(hausdorff (m + 2) X).real (ball p t) / (euclideanUnitVolume (m + 2) * t ^ (m + 2)) - 1| ≤ 1 / 4)
    (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic)
    (_hbase : ∀ i j, ∀ᵐ x ∂(hausdorff (m + 2) X).restrict (ball p (distanceSourceRadius r0 i / 64)),
      localGamma (hausdorff (m + 2) X) hX.quadratic (u j) (u j) x ≤ L ^ 2)
    (F : ℕ → Euclidean (m + 2) ≃L[ℝ] Euclidean (m + 2))
    (v : ℕ → X → Euclidean (m + 2)) (_hδ : 0 ≤ δ)
    (_hδ1 : radialNormalizationRestrictionConstant (m + 2) * δ ≤ 1)
    (_hsmall : ((m + 2 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio (m + 1) * δ) ≤ 1 / 64)
    (_hexact : ∀ i, IsExactMeanNormalization (hausdorff (m + 2) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
      (ball p (2 * distanceSourceRadius r0 i)) measurableSet_ball (F i))
    (_hfirst : ∀ i, FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p
      (2 * distanceSourceRadius r0 i) δ (transformedColumn (hausdorff (m + 2) X) hX.quadratic u (F i)) (v i))
    (_hmetric : ∀ i, IsPointedApproximation p 0 (distanceSourceRadius r0 i / 64) 4 δ
      (fun x => (distanceSourceRadius r0 i / 64)⁻¹ • (v i x - v i p)))
    (_hf : ∀ i, ∀ᵐ x ∂(hausdorff (m + 2) X).restrict (ball p (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff (m + 2) X) hX.quadratic (T.replacement i) (T.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (χ : ∀ i, GoodLaplacianCutoff (hausdorff (m + 2) X) hX.quadratic p (distanceSourceRadius r0 i / 64) Cχ)
    (_hfit : ∀ i, HasNormalizedAffineImprovement hX u p (distanceSourceRadius r0 i / 64) ((1 / 2 : ℝ) ^ d))
    (V : X → Euclidean (m + 2))
    (_hu : FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p r0 ε u V)
    (_hcurv : ∀ i, -κ₀ ≤ K * (distanceSourceRadius r0 i / 64) ^ 2)
    ,
    ∀ i,
      ∃ coeff : Fin (m + 2) → Euclidean (m + 2),
      ∃ g : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic,
      let μ := hausdorff (m + 2) X
      let s := distanceSourceRadius r0 i
      let r := s / 64
      let E := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant (m + 2) Cχ * δ)
        (normalizedPoissonDefect μ hX.quadratic S) i
      ‖Matrix.toEuclideanCLM (n := Fin (m + 2)) (𝕜 := ℝ) (radialCoefficientMatrix (F i) coeff) -
          ContinuousLinearMap.id ℝ (Euclidean (m + 2))‖ ≤
        ((m + 2 : ℕ) : ℝ) ^ 2 *
          Real.sqrt (2 * Ca ^ 2 * (D ^ 2 * E + radialFitQualitativeConstant (m + 2) Cχ * δ)) ∧
      ∀ j,
      let H := centeredAffineSobolev μ hX.quadratic u (χ i).sobolev (V p) (coeff j)
      (SobolevSpace.toLp μ hX.quadratic (g j) =ᵐ[μ.restrict (ball p r)]
        localGamma μ hX.quadratic (T.replacement i)
          (sobolevColumnMap μ hX.quadratic u (F i (EuclideanSpace.single j 1)))) ∧
      ‖normalizeLocalL2 μ (ball p r) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hX.quadratic (ball p r) (g j - H))‖ ^ 2 ≤
        (2 * D ^ 2 + 8192 * (((m + 2 : ℕ) : ℝ) * 2) ^ 2 * B *
          ((4 / (3 * euclideanUnitVolume (m + 2))) * (64 : ℝ) ^ (m + 2))) * r ^ 2 * E ∧
      (μ.real (ball p (r / 2)))⁻¹ *
        (∫ x in ball p (r / 2), localGamma μ hX.quadratic (g j - H) (g j - H) x ∂μ) ≤
        radialEnergyConstant K (m + 2) Cg 1 A B J Cχ *
          ((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ (m + 2))⁻¹ * D ^ 2 +
            (4 / (3 * euclideanUnitVolume (m + 2))) * (128 : ℝ) ^ (m + 2)) * E := by
  obtain ⟨Cg, D, hCg, hD, hallscalar⟩ := dyadic_radial_value_energy_uniform m hX hhessian
    hmean hgradient hB hJ hA hCχ hκ₀ hd
  obtain ⟨Ca, hCa, hallcoeff⟩ := dyadic_radial_coefficient_bound_uniform m hX hgradient hκ₀
  refine ⟨Cg, D, Ca, hCg, hD, hCa, ?_⟩
  intro a κ r0 C L δ ε p ha hκ hK hr01 hscale hBG S T hP hquarter u hbase F v hδ
    hδ1 hsmall hexact hfirst hmetric hf χ hfit V hu hcurv
  classical
  let μ := hausdorff (m + 2) X
  let hQ := hX.quadratic
  let E := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant (m + 2) Cχ * δ)
    (normalizedPoissonDefect μ hQ S)
  have hscalar := hallscalar ha hκ hK hr01 hscale hBG S T hP hquarter u hbase F v hδ
    hδ1 hsmall hexact hfirst hmetric hf χ hfit V hu hcurv
  have hcoeff := hallcoeff ha hCχ hD.le hscale hBG S T hquarter u hbase F v hδ hδ1 hsmall
    hexact hfirst hmetric χ V hu hcurv
  obtain ⟨_, _, hE⟩ := radial_fit_pinching_envelope_budget S hκ hCχ hδ hP
  intro i
  have hchoose (j : Fin (m + 2)) :
      ∃ a : Euclidean (m + 2), ∃ g : SobolevSpace μ hQ,
      ‖(F i).symm (a - F i (EuclideanSpace.single j 1))‖ ^ 2 ≤
        2 * Ca ^ 2 * (D ^ 2 * E i + radialFitQualitativeConstant (m + 2) Cχ * δ) ∧
      let r := distanceSourceRadius r0 i / 64
      let H := centeredAffineSobolev μ hQ u (χ i).sobolev (V p) a
      (SobolevSpace.toLp μ hQ g =ᵐ[μ.restrict (ball p r)]
        localGamma μ hQ (T.replacement i)
          (sobolevColumnMap μ hQ u (F i (EuclideanSpace.single j 1)))) ∧
      ‖normalizeLocalL2 μ (ball p r) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hQ (ball p r) (g - H))‖ ^ 2 ≤
        (2 * D ^ 2 + 8192 * (((m + 2 : ℕ) : ℝ) * 2) ^ 2 * B *
          ((4 / (3 * euclideanUnitVolume (m + 2))) * (64 : ℝ) ^ (m + 2))) * r ^ 2 * E i ∧
      (μ.real (ball p (r / 2)))⁻¹ *
        (∫ x in ball p (r / 2), localGamma μ hQ (g - H) (g - H) x ∂μ) ≤
        radialEnergyConstant K (m + 2) Cg 1 A B J Cχ *
          ((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ (m + 2))⁻¹ * D ^ 2 +
            (4 / (3 * euclideanUnitVolume (m + 2))) * (128 : ℝ) ^ (m + 2)) * E i := by
    let b := F i (EuclideanSpace.single j 1)
    have hb : b ≠ 0 := by
      intro hz
      have he := congrArg (fun w => ((F i).symm w) j) hz
      simp [b] at he
    obtain ⟨a, g, hall⟩ := hscalar b hb
    have ha := hcoeff b a E (fun k => (hE k).1) (fun k => (hall k).2.1) i
    have hi := hall i
    have hunit : ‖(F i).symm b‖ = 1 := by simp [b]
    rw [hunit] at ha hi
    simp only [one_pow, mul_one] at ha hi
    refine ⟨a i, g i, ?_, ?_⟩
    · exact ha
    · exact ⟨hi.1, hi.2.2.1, hi.2.2.2⟩
  choose coeff g hrow using hchoose
  refine ⟨coeff, g, ?_, fun j => (hrow j).2⟩
  apply radialCoefficientMatrix_sub_id_norm _ _ (Real.sqrt_nonneg _)
  intro j
  have hh := Real.sqrt_le_sqrt (hrow j).1
  simpa only [Real.sqrt_sq (norm_nonneg _)] using hh

end RegularPointCoordinates

end

end OAI
