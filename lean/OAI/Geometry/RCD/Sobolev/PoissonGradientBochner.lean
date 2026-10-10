import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Sobolev.PoissonEnergySubsolution
import OAI.Geometry.RCD.Sobolev.PoissonGradientBoundedness
import OAI.Geometry.RCD.Sobolev.PoissonBallEnergy
import OAI.Geometry.RCD.Sobolev.SubsolutionL1Mean

namespace OAI

/-! # Scale-uniform Poisson gradient control from the energy subsolution -/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The Bochner mean bound removes the small-radius restriction from the
heat construction of a locally bounded gradient. -/
theorem NoncollapsedRCD.poisson_gradient_bochner {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker)
    (hess : LocalPoissonHessianInput hX) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (r : ℝ), 0 < r → -1 ≤ K*r^2 →
      ∀ (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ) (A : ℝ≥0),
      IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) f c →
      (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic f x| ≤ A) →
      ∀ᵐ x ∂(hausdorff n X).restrict (ball p (r/2)),
        localGamma (hausdorff n X) hX.quadratic f f x ≤ (C*((A:ℝ)/r+|c| *r))^2 := by
  obtain ⟨M,hM,hmean⟩ := hX.subsolution_l1_mean_value hn 2 (by norm_num)
  obtain ⟨D,hD,hvolume⟩ := hX.rescaled_ball_volume_factor hn (a := 16) (δ := 1/4)
    (by norm_num) (by norm_num) (by norm_num)
  let C := 1+4*M*D
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hMD : 0 ≤ M*D := mul_nonneg hM0 hD0
  have hC : 1 ≤ C := by dsimp only [C]; nlinarith
  refine ⟨C,hC,?_⟩
  intro p r hr hcurv f c A hf hA
  let μ := hausdorff n X
  let κ := max (-K) 0
  have hκ : 0 ≤ κ := le_max_right _ _
  have hκK : -κ ≤ K := by have hh := le_max_left (-K) 0; dsimp only [κ]; linarith
  have hκr : (2*κ)*r^2 ≤ 2 := by
    by_cases hK : 0 ≤ K
    · have he : κ = 0 := max_eq_right (neg_nonpos.mpr hK)
      rw [he]; norm_num
    · have he : κ = -K := max_eq_left (neg_nonneg.mpr (le_of_not_ge hK))
      rw [he]; nlinarith only [hcurv]
  have hf4 := hf.mono μ hX.quadratic measurableSet_ball
    (ball_subset_ball (by linarith : 4*r ≤ 8*r))
  obtain ⟨L,hL⟩ := hX.poisson_gradient_locally_bounded hn hk hg p r hr f c A hf
    (ae_restrict_of_ae hA)
  obtain ⟨e,B,hB,herep,hebound,hesub⟩ := hess.energy_subsolution κ hκ hκK p (r/2)
    (by positivity) f c L (by simpa only [show 8*(r/2) = 4*r by ring] using hf4)
    (by simpa only [show 8*(r/2) = 4*r by ring] using hL)
  rw [show 2*(r/2) = r by ring] at herep hesub
  have hepos : ∀ᵐ x ∂μ.restrict (ball p r),
      0 ≤ SobolevSpace.toLp μ hX.quadratic e x ∧ SobolevSpace.toLp μ hX.quadratic e x ≤ B := by
    filter_upwards [herep,ae_restrict_of_ae (localGamma_self μ hX.quadratic f),
      ae_restrict_of_ae hebound] with x he hsq hb
    constructor
    · rw [he,hsq]; positivity
    · exact (le_abs_self _).trans hb
  have hm := hmean p r hr hcurv e (2*κ) B (by positivity) hκr hB hesub hepos
  have henergy := hX.poisson_ball_energy p r hr f c A hf4 hA
  have hi : (∫ x in ball p r, SobolevSpace.toLp μ hX.quadratic e x ∂μ) ≤
      (2*|c| *A+4*(A:ℝ)^2*(r⁻¹)^2)*μ.real (ball p (4*r)) := by
    rw [integral_congr_ae herep]
    exact henergy
  have hcurv4 : -16 ≤ K*(4*r)^2 := by nlinarith only [hcurv]
  have hv : μ.real (ball p (4*r)) ≤ D*μ.real (ball p r) := by
    have hh := hvolume p (4*r) (by positivity) hcurv4 p (by simp; positivity)
    simpa only [show (1/4:ℝ)*(4*r) = r by ring] using hh
  have hV : 0 < μ.real (ball p r) := ENNReal.toReal_pos (hX.fullSupport p r hr).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  let E := 2*|c| *A+4*(A:ℝ)^2*(r⁻¹)^2
  have hE : 0 ≤ E := by positivity
  have hint : (μ.real (ball p r))⁻¹*(∫ x in ball p r, SobolevSpace.toLp μ hX.quadratic e x ∂μ) ≤ D*E := by
    calc
      _ ≤ (μ.real (ball p r))⁻¹*(E*(D*μ.real (ball p r))) :=
        mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left hv hE)) (inv_nonneg.mpr hV.le)
      _ = _ := by field_simp
  have halg : M*(D*E) ≤ (C*((A:ℝ)/r+|c| *r))^2 := by
    have hAE : E ≤ 4*((A:ℝ)/r+|c| *r)^2 := by
      have heq : E = 2*((A:ℝ)/r)*(|c| *r)+4*((A:ℝ)/r)^2 := by
        dsimp only [E]
        field_simp
      rw [heq]
      nlinarith [sq_nonneg (|c| *r),
        mul_nonneg (div_nonneg A.coe_nonneg hr.le) (mul_nonneg (abs_nonneg c) hr.le)]
    have hc2 : 4*M*D ≤ C^2 := by dsimp only [C]; nlinarith [sq_nonneg (4*M*D)]
    calc
      _ ≤ (4*M*D)*((A:ℝ)/r+|c| *r)^2 := by
        have hh := mul_le_mul_of_nonneg_left hAE hMD
        nlinarith only [hh]
      _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
  filter_upwards [hm,ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (by linarith : r/2 ≤ r)) herep] with x hx he
  rw [he] at hx
  have hh : M*(μ.real (ball p r))⁻¹*(∫ z in ball p r,
      SobolevSpace.toLp μ hX.quadratic e z ∂μ) ≤ M*(D*E) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hint hM0
  exact hx.trans (hh.trans halg)

end RegularPointCoordinates

end

end OAI
