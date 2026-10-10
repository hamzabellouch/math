import OAI.Geometry.IsometricImmersion.Metrics.MetricCompatibility
import OAI.Geometry.IsometricImmersion.Calculus.QuotientCalculus
import OAI.Geometry.IsometricImmersion.Darboux.DriftBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

def hessianQuotient (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  covHessian g z p 0 1 / covHessian g z p 1 1

def darbouxG (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  heightEnergy g z p / (covHessian g z p 1 1) ^ 2

def connectionTraceY (g : MetricField) (p : Coord) : ℝ :=
  christoffel g 0 0 1 p + christoffel g 1 1 1 p

def driftJ (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  (g p 0 0 - hessianQuotient g z p * g p 0 1) * coordPartial 1 z p -
    (g p 0 1 - hessianQuotient g z p * g p 1 1) * coordPartial 0 z p

def curvatureDriftError (g : MetricField) (z : Coord → ℝ) : Coord → ℝ :=
  explicitDriftError (fun p => covHessian g z p 1 1) (heightEnergy g z)
    (connectionTraceY g) (driftJ g z)

theorem curvatureDriftError_eq (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    curvatureDriftError g z p =
      darbouxG g z p *
        (connectionTraceY g p -
          coordPartial 1 (fun q => covHessian g z q 1 1) p / covHessian g z p 1 1) +
        driftJ g z p / covHessian g z p 1 1 := rfl

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem hessianQuotient_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (hessianQuotient g z) U :=
  (covHessian_contDiffOn hg hU hz 0 1).div (covHessian_contDiffOn hg hU hz 1 1) hyy

theorem darbouxG_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (darbouxG g z) U :=
  (heightEnergy_contDiffOn hg hU hz).div ((covHessian_contDiffOn hg hU hz 1 1).pow 2)
    (fun p hp => pow_ne_zero 2 (hyy p hp))

theorem connectionTraceY_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (connectionTraceY g) U :=
  (christoffel_contDiffOn hg hU 0 0 1).add (christoffel_contDiffOn hg hU 1 1 1)

theorem driftJ_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (driftJ g z) U := by
  have hq := hessianQuotient_contDiffOn hg hU hz hyy
  exact (((hg.1 0 0).sub (hq.mul (hg.1 0 1))).mul (partial_contDiffOn hz hU 1)).sub
    (((hg.1 0 1).sub (hq.mul (hg.1 1 1))).mul (partial_contDiffOn hz hU 0))

theorem curvatureDriftError_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (curvatureDriftError g z) U :=
  explicitDriftError_contDiffOn hU (covHessian_contDiffOn hg hU hz 1 1)
    (heightEnergy_contDiffOn hg hU hz) (connectionTraceY_contDiffOn hg hU)
    (driftJ_contDiffOn hg hU hz hyy) hyy

theorem curvatureWeightedDriftError_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => gaussianCurvature g p * curvatureDriftError g z p) U :=
  (gaussianCurvature_contDiffOn hg hU).mul (curvatureDriftError_contDiffOn hg hU hz hyy)

theorem darbouxG_pos (g : MetricField) (z : Coord → ℝ) (p : Coord)
    (hE : 0 < heightEnergy g z p) (hyy : covHessian g z p 1 1 ≠ 0) :
    0 < darbouxG g z p :=
  height_energy_quotient_pos (heightEnergy g z p) (covHessian g z p 1 1) hE hyy

theorem curvatureDriftError_bound
    (g : MetricField) (z : Coord → ℝ) (p : Coord) (c BE Bh BT BJ : ℝ)
    (hc : 0 < c) (hh : c ≤ |covHessian g z p 1 1|)
    (hE : |heightEnergy g z p| ≤ BE)
    (hhy : |coordPartial 1 (fun q => covHessian g z q 1 1) p| ≤ Bh)
    (hT : |connectionTraceY g p| ≤ BT) (hJ : |driftJ g z p| ≤ BJ) :
    |curvatureDriftError g z p| ≤ BE / c ^ 2 * (BT + Bh / c) + BJ / c :=
  explicitDriftError_pointwise_bound (fun q => covHessian g z q 1 1)
    (heightEnergy g z) (connectionTraceY g) (driftJ g z) p c BE Bh BT BJ
      hc hh hE hhy hT hJ

theorem driftJ_bound
    (g : MetricField) (z : Coord → ℝ) (p : Coord) (M : ℝ)
    (hMetric : ∀ i j : Fin 2, |g p i j| ≤ M)
    (hHeight : ∀ i : Fin 2, |coordPartial i z p| ≤ M)
    (hq : |hessianQuotient g z p| ≤ (1 / 100 : ℝ)) :
    |driftJ g z p| ≤ (202 / 100 : ℝ) * M ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg (g p 0 0)).trans (hMetric 0 0)
  have heps : (0 : ℝ) ≤ 1 / 100 := by norm_num
  have htriangle (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le a 0 b
  have hqg (i j : Fin 2) :
      |hessianQuotient g z p * g p i j| ≤ (1 / 100 : ℝ) * M := by
    rw [abs_mul]
    exact mul_le_mul hq (hMetric i j) (abs_nonneg _) heps
  have hfactor (a b c d : Fin 2) :
      |g p a b - hessianQuotient g z p * g p c d| ≤ M + (1 / 100 : ℝ) * M :=
    (htriangle _ _).trans (add_le_add (hMetric a b) (hqg c d))
  have hfactor_nonneg : 0 ≤ M + (1 / 100 : ℝ) * M :=
    add_nonneg hM (mul_nonneg heps hM)
  calc
    |driftJ g z p| ≤
        |(g p 0 0 - hessianQuotient g z p * g p 0 1) * coordPartial 1 z p| +
          |(g p 0 1 - hessianQuotient g z p * g p 1 1) * coordPartial 0 z p| :=
      htriangle _ _
    _ = |g p 0 0 - hessianQuotient g z p * g p 0 1| * |coordPartial 1 z p| +
          |g p 0 1 - hessianQuotient g z p * g p 1 1| * |coordPartial 0 z p| := by
      rw [abs_mul, abs_mul]
    _ ≤ (M + (1 / 100 : ℝ) * M) * M + (M + (1 / 100 : ℝ) * M) * M :=
      add_le_add
        (mul_le_mul (hfactor 0 0 0 1) (hHeight 1) (abs_nonneg _) hfactor_nonneg)
        (mul_le_mul (hfactor 0 1 1 1) (hHeight 0) (abs_nonneg _) hfactor_nonneg)
    _ = (202 / 100 : ℝ) * M ^ 2 := by ring

theorem curvatureDriftError_bound_from_low_data
    (g : MetricField) (z : Coord → ℝ) (p : Coord) (c BE Bh BT M : ℝ)
    (hc : 0 < c) (hh : c ≤ |covHessian g z p 1 1|)
    (hE : |heightEnergy g z p| ≤ BE)
    (hhy : |coordPartial 1 (fun q => covHessian g z q 1 1) p| ≤ Bh)
    (hT : |connectionTraceY g p| ≤ BT)
    (hMetric : ∀ i j : Fin 2, |g p i j| ≤ M)
    (hHeight : ∀ i : Fin 2, |coordPartial i z p| ≤ M)
    (hq : |hessianQuotient g z p| ≤ (1 / 100 : ℝ)) :
    |curvatureDriftError g z p| ≤
      BE / c ^ 2 * (BT + Bh / c) + ((202 / 100 : ℝ) * M ^ 2) / c :=
  curvatureDriftError_bound g z p c BE Bh BT ((202 / 100 : ℝ) * M ^ 2)
    hc hh hE hhy hT (driftJ_bound g z p M hMetric hHeight hq)

end SmoothLocal.Geometry

end

end OAI
