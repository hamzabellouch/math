import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Sobolev.FixedCutoffNeighborhood
import OAI.Geometry.RCD.Heat.UniformHeatControlsAt
import OAI.Geometry.RCD.Heat.UniformHeatBase
import OAI.Geometry.RCD.Metric.UniformMassBackground

namespace OAI

/-! # Cumulative heat estimates on a regular-point neighborhood

All centers use a common harmonic map, full positive Bochner measure,
cutoff, regularizer, and starting index.
-/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Cumulative heat comparisons hold with common constants throughout one
neighborhood of an all-tangents regular point. No heat comparison or
coordinate conclusion is assumed in the inputs. -/
theorem regular_neighborhood_cumulative_heat {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [(hausdorff (m + 2) X).Regular]
    {p : X} {a : ℝ} (ha : 0 ≤ a)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 2) p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff (m + 2) X) (m + 2) p
      (euclideanUnitVolume (m + 2)))
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff (m + 2) X) (m + 2) p)
    (hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff (m + 2) X)
      (comparisonModelVolume (m + 1) a) y (euclideanUnitVolume (m + 2)))
    (hinitial : LocalInitialSplittingInput hX) (htrans : LocalTransformationInput hX)
    (hsplit : LocalFlatSplittingInput hX) (hrigidity : UniformRegularFlatnessInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker) :
    ∃ R : ℝ, ∃ hR : 0 < R, ∃ lambda : ℝ, ∃ hlambda : 0 < lambda,
    ∃ (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic)
      (M : PositiveBilinearMeasure X (Euclidean (m + 2))) (Ccut : ℝ)
      (χ : GoodLaplacianCutoff (hausdorff (m + 2) X) hX.quadratic p (3 * R / 8) Ccut)
      (J : ℕ) (A B D : ℝ),
      R ≤ 1 ∧ 0 < A ∧ 0 < B ∧ 0 < D ∧
      ∀ q ∈ ball p (R / 32), ∀ (xi : Euclidean (m + 2)) (k : ℕ),
        let Q := dyadicHeatGramAt (hausdorff (m + 2) X) hX.quadratic hk
          (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u) χ q hR hlambda
        let H := ⟪xi, (Q (J + k)).symm xi⟫_ℝ
        let mass := ∑ i ∈ Finset.range k,
          ⟪(Q (J + i)).symm xi, dyadicBochnerMass M (m + 2) q R (J + i) ((Q (J + i)).symm xi)⟫_ℝ
        (∑ i ∈ Finset.range k,
          ⟪(Q (J + i)).symm xi, dyadicBochnerEnvelope M (m + 2) q R (J + i) ((Q (J + i)).symm xi)⟫_ℝ) ≤ A * H ∧
        ‖xi‖ ^ 2 + mass ≤ B * H ∧ H ≤ D * (‖xi‖ ^ 2 + mass) := by
  classical
  let μ := hausdorff (m + 2) X
  let omega := euclideanUnitVolume (m + 2)
  have homega : 0 < omega := euclideanUnitVolume_pos _
  obtain ⟨Ccut, hCcut, hcut⟩ := hcutoff (by omega)
  let lambda := 8 * |K| * ((m + 2 : ℕ) : ℝ) ^ 2 + 1
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hVlo : 0 < omega / (2 * (2 : ℝ) ^ (m + 2)) := by positivity
  have hVhi : 0 < (3 / 2 : ℝ) * omega := by positivity
  obtain ⟨ε, εmass, C, N, hε, hε1, hεmass, hC, habsorb, hcontrols⟩ :=
    uniform_heat_controls_at_of_splitting m hX ha hBG hk hg
      (L := 4 * ((m + 2 : ℕ) : ℝ) ^ 2) (B := 2)
      (C := Ccut) (η := 1) (lambda := lambda)
      (by positivity) (by norm_num) hVlo hVhi (by linarith) (by norm_num) hlambda
  obtain ⟨R, e, hR, hRsmall, hscale, hcurv, he, he1, L, u, v, M, hL, _hu, hG, hvol, hfamily, _hmetric⟩ :=
    regular_uniform_dyadic_data (m + 1) hX (by omega) ha hcompact hregular hvolume hmeasured hBG
      hdensity hinitial htrans hsplit hrigidity hbochner zero_lt_one hε
  have hR1 : R ≤ 1 := by linarith
  have hscale' : a * (3 * R) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (show 3 * R ≤ 48 * R by linarith) ha
    linarith
  have hcurv' : |K| * R ^ 2 ≤ ε := by
    have hh := mul_le_mul_of_nonneg_left
      (show R ^ 2 ≤ (16 * R) ^ 2 by nlinarith [sq_nonneg R]) (abs_nonneg K)
    exact hh.trans hcurv
  have hreg : 2 * |K| * (L : ℝ) ^ 2 + 1 ≤ lambda := by
    have hh := mul_le_mul_of_nonneg_left hL (show 0 ≤ 2 * |K| by positivity)
    dsimp only [lambda]
    nlinarith only [hh]
  let G := fun z => Classical.choice (hG z)
  obtain ⟨χ, J₀, hχ⟩ := exists_fixed_cutoff_neighborhood μ hX.quadratic hk G hg hR homega
    (hcurv.trans hε1) hvol (hcut p)
  let J := max 4 (max N J₀)
  obtain ⟨b, hb, hbackground⟩ := exists_uniform_mass_background M (m + 2) hR J
  obtain ⟨T, hT, hbase⟩ := exists_uniform_dyadic_heat_base μ hX.quadratic hk G χ
    (show 3 * R / 8 < 4 * R by linarith) hR hlambda J
  obtain ⟨A, B, D, hA, hB, hD, hresult⟩ :=
    exists_uniform_heat_cumulative_constants (E := Euclidean (m + 2)) hb hT hεmass hC habsorb
  refine ⟨R, hR, lambda, hlambda, u, M, Ccut, χ, J, A, B, D, hR1, hA, hB, hD, ?_⟩
  intro q hq
  have hqp : dist q p < R / 32 := hq
  have hqR : q ∈ ball p R := by change dist q p < R; linarith
  obtain ⟨S, hexact, hfirst, hS0, _hfirstv, _hmetricS⟩ := hfamily q hqR
  have hsub : ball q (2 * (2 * R)) ⊆ ball p (2 * (4 * R)) := by
    intro x hx
    have hxq : dist x q < 2 * (2 * R) := hx
    change dist x p < 2 * (4 * R)
    have hh := dist_triangle x q p
    linarith
  let Gq := fun z => (G z).restrict μ hX.quadratic hsub
  have hvolq : ∀ y, dist q y ≤ 2 * R → ∀ s, 0 < s → s ≤ R →
      |μ.real (ball y s) / (omega * s ^ (m + 2)) - 1| ≤ 1 / 2 := by
    intro y hy s hs hsR
    apply hvol y ?_ s hs (by linarith)
    have hh := dist_triangle p q y
    rw [dist_comm p q] at hh
    linarith
  have hgradient : ∀ z : Euclidean (m + 2), ∀ᵐ x ∂μ.restrict (ball q R),
      localGamma μ hX.quadratic (sobolevColumnMap μ hX.quadratic u z)
        (sobolevColumnMap μ hX.quadratic u z) x ≤
          (4 * ((m + 2 : ℕ) : ℝ) ^ 2) * ‖z‖ ^ 2 := by
    intro z
    filter_upwards [LocalHarmonicEnergy.gamma_bound_on_smaller_ball μ hX.quadratic Gq
      (show R ≤ 2 * (2 * R) by linarith) z] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_right hL (sq_nonneg _))
  have hc := hcontrols R hR hR1 hscale' u M S q ε L Gq hε.le le_rfl hcurv' hreg hS0
    hexact hfirst (hcut q) (dyadic_heat_volumes_of_common_regime μ (m + 2) q hR homega hvolq)
    hgradient p (4 * R) (3 * R / 8) Ccut G χ (by positivity) (by linarith)
    (hχ q hq).1 (hχ q hq).2.1 J₀ (hχ q hq).2.2 J le_rfl
  let Q := dyadicHeatGramAt μ hX.quadratic hk (sobolevColumnMap μ hX.quadratic u) χ q hR hlambda
  apply hresult Q (dyadicBochnerMass M (m + 2) q R) (dyadicBochnerEnvelope M (m + 2) q R) J
    (dyadicHeatGramAt_isPositive μ hX.quadratic hk _ χ q hR hlambda)
    (dyadicBochnerMass_isPositive M (m + 2) q hR.le) hc.1.step hc.1.decrement hc.1.small
    (hbackground q)
  · exact fun z => (hbase q z).1
  · exact fun z => (hbase q z).2

end RegularPointCoordinates

end

end OAI
