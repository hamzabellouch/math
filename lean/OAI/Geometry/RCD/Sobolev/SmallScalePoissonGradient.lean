import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Sobolev.CutoffPoissonRepresentative
import OAI.Geometry.RCD.Sobolev.PoissonAnnularEnergy
import OAI.Geometry.RCD.Sobolev.LocalRepresentativeGradient
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent
import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # Small-scale interior Poisson gradient estimate from the heat equation -/

open Set Filter Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A quantitative interior gradient estimate, with both cutoffs constructed
from the RCD condition and no gradient assumption on the solution. -/
theorem NoncollapsedRCD.small_scale_poisson_gradient {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (p : X) (R : ℝ), 0 < R → R ≤ 1 → -1 ≤ K*(4*R)^2 →
      ∀ (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ) (A : ℝ≥0),
      IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (16*R)) f c →
      (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp _ _ f x| ≤ A) →
      ∀ᵐ x ∂(hausdorff n X).restrict (ball p (R/16)),
        localGamma (hausdorff n X) hX.quadratic f f x ≤ (M*(A/R+|c| *R))^2 := by
  obtain ⟨J,hJ,hrep⟩ := hX.cutoff_poisson_representative hn hk hg
  obtain ⟨C,hC,hcut⟩ := hX.goodCutoffInput hn
  obtain ⟨V,hV,hvol⟩ := hX.rescaled_ball_volume_factor hn
    (a := 256) (δ := 1/16) (by norm_num) (by norm_num) (by norm_num)
  let B := 2+5*C^2
  let P := Real.exp |K| *(3+2*C)+J*V*B
  let M := P+16
  have hC0 : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 1).trans hC
  have hV0 : 0 ≤ V := (by norm_num : (0:ℝ) ≤ 1).trans hV
  have hB : 0 < B := by dsimp [B]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨M,by dsimp [M]; linarith,?_⟩
  intro p R hR hR1 hcurv f c A hf hA
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  by_cases hAz : (A:ℝ) = 0
  · filter_upwards [ae_restrict_of_ae hA,ae_restrict_of_ae (localGamma_self μ hX.quadratic f),
      ae_restrict_of_ae (SobolevSpace.minimalSlope_zero_on_level μ hX.quadratic f 0)] with x ha he hz
    have hfz : SobolevSpace.toLp μ hX.quadratic f x = 0 := abs_nonpos_iff.mp (hAz ▸ ha)
    rw [he,hz hfz,zero_pow (by decide)]
    exact sq_nonneg _
  have hApos : 0 < (A:ℝ) := lt_of_le_of_ne A.coe_nonneg (Ne.symm hAz)
  have hcurvR : -1 ≤ K*R^2 := by nlinarith only [hcurv]
  have hcurv16 : -(256:ℝ) ≤ K*(16*R)^2 := by nlinarith only [hcurvR]
  obtain ⟨χ⟩ := hcut p R hR hcurvR
  obtain ⟨η⟩ := hcut p (4*R) (by positivity) hcurv
  have hinside : closedBall p (2*R) ⊆ ball p (16*R) := closedBall_subset_ball (by linarith)
  have hηsupp : tsupport (η.weight : X → ℝ) ⊆ ball p (16*R) :=
    (η.tsupport_subset μ hX.quadratic).trans (closedBall_subset_ball (by linarith))
  have hηone : ∀ x, R ≤ dist x p → dist x p ≤ 2*R → η.weight x = 1 := by
    intro x _ hx
    apply η.one x
    change dist x p < 4*R
    linarith
  have hsource := hf.cutoff_cross_L1_le μ hX.quadratic
    (hX.finiteOnBounded _ isBounded_ball).ne f η.sobolev c A hApos hA
    η.lipschitz (η.hasCompactSupport μ hX.quadratic) η.bounds hηsupp η.representative
    hR hC0 χ hinside hηone
  rw [Real.coe_toNNReal _ (by positivity : 0 ≤ C/(4*R))] at hsource
  let W := μ.real (ball p R)
  have hW : 0 < W := ENNReal.toReal_pos (hX.fullSupport p R hR).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hvol' : μ.real (ball p (16*R)) ≤ V*W := by
    have hh := hvol p (16*R) (by positivity) hcurv16 p (by simp; positivity)
    simpa only [show (1/16:ℝ)*(16*R) = R by ring] using hh
  have hsourcecoef : 2*|c|+4*(A:ℝ)*(C/(4*R))^2+(A:ℝ)*(C/R)^2 ≤
      B*((A:ℝ)/R^2+|c|) := by
    dsimp only [B]
    field_simp
    nlinarith [mul_nonneg (abs_nonneg c) (sq_nonneg C),mul_nonneg A.coe_nonneg (sq_nonneg C)]
  have hsource' : (∫ z, |2*localGamma μ hX.quadratic f χ.sobolev z| ∂μ) ≤
      B*((A:ℝ)/R^2+|c|)*V*W := by
    calc
      _ ≤ (2*|c|+4*(A:ℝ)*(C/(4*R))^2+(A:ℝ)*(C/R)^2)*μ.real (ball p (16*R)) := hsource
      _ ≤ (B*((A:ℝ)/R^2+|c|))*(V*W) :=
        mul_le_mul hsourcecoef hvol' (measureReal_nonneg) (by positivity)
      _ = _ := by ring
  have hT1 : R^2 ≤ 1 := by nlinarith
  obtain ⟨v,hv,he⟩ := hrep p R (R^2) C hR hcurvR (sq_pos_of_pos hR) hT1 le_rfl hC0
    (ball p (16*R)) f c hf A hA χ hinside
  rw [Real.sqrt_sq hR.le] at hv
  let Q := Real.exp (|K| *R^2)*((A:ℝ)/R+2*(|c|+A*(C/R^2))*R)+
    (J/(R*W)*(∫ z, |2*localGamma μ hX.quadratic f χ.sobolev z| ∂μ))*R^2
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hQ : Q ≤ P*((A:ℝ)/R+|c| *R) := by
    have hexp : Real.exp (|K| *R^2) ≤ Real.exp |K| :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hT1 (abs_nonneg K)])
    have hann : (J/(R*W)*(∫ z, |2*localGamma μ hX.quadratic f χ.sobolev z| ∂μ))*R^2 ≤
        J*V*B*((A:ℝ)/R+|c| *R) := by
      calc
        _ ≤ (J/(R*W)*(B*((A:ℝ)/R^2+|c|)*V*W))*R^2 := by gcongr
        _ = _ := by field_simp
    have hbounded : (A:ℝ)/R+2*(|c|+A*(C/R^2))*R ≤
        (3+2*C)*((A:ℝ)/R+|c| *R) := by
      field_simp
      nlinarith only [A.coe_nonneg,mul_nonneg (sq_nonneg R) (abs_nonneg c),
        mul_nonneg (sq_nonneg R) (mul_nonneg hC0 (abs_nonneg c))]
    dsimp only [Q,P]
    have hh := mul_le_mul hexp hbounded (by positivity) (by positivity)
    nlinarith only [hh,hann]
  have hg0 := localGamma_le_of_lipschitz_representative μ hX.quadratic f v Q.toNNReal A hv
    p (R/16) (by positivity)
    (by simpa only [show 2*(R/16) = R/8 by ring] using he) (ae_restrict_of_ae hA)
  filter_upwards [hg0] with x hx
  have hcoeff : (Q.toNNReal:ℝ)+(A:ℝ)/(R/16) ≤ M*((A:ℝ)/R+|c| *R) := by
    rw [Real.coe_toNNReal _ hQ0]
    dsimp only [M]
    have hid : (A:ℝ)/(R/16) = 16*((A:ℝ)/R) := by ring
    rw [hid]
    nlinarith only [hQ,mul_nonneg (abs_nonneg c) hR.le]
  exact hx.trans (pow_le_pow_left₀ (by positivity) hcoeff 2)

end RegularPointCoordinates

end

end OAI
