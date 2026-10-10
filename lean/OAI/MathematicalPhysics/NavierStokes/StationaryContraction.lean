import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The conditional stationary correction argument

Exact rational estimates and the Banach fixed-point step from OpenAI,
*Stationary instability and nonuniqueness for axisymmetric swirl-free
Navier–Stokes*, section “Correcting the stationary profile”. The inverse,
change of variables and bilinear map satisfy explicit operator norm hypotheses.
-/

noncomputable section

namespace StationaryNS

/-- The weight in the stationary profile norm `D`. -/
def kappa : ℝ := 3 / 25

/-- Coercivity margin, `η = .29`. -/
def eta : ℝ := 29 / 100

/-- Upper bound `F₀ = 5.1 × 10⁻⁷` for the stationary residual. -/
def residualBound : ℝ := 51 / 100000000

/-- Upper bound for the transformed nonlinearity, `c = .271`. -/
def nonlinearBound : ℝ := 271 / 1000

/-- Radius of the contraction ball, `r₀ = 2 F₀ / η`. -/
def correctionRadius : ℝ := 2 * residualBound / eta

/-- The strict correction bound `2.216 × 10⁻⁴`. -/
def targetError : ℝ := 277 / 1250000

/-- The Lipschitz bound `.027` is strictly less than one. -/
theorem lipschitz_budget :
    2 * nonlinearBound * 63 ^ 2 * correctionRadius / eta < (27 / 1000 : ℝ) := by
  norm_num [nonlinearBound, correctionRadius, residualBound, eta]

/-- The norm bound on the actual correction is strictly below the stated decimal. -/
theorem correction_budget : (63 : ℝ) * correctionRadius < targetError := by
  norm_num [correctionRadius, residualBound, eta, targetError]

/-- The closed-ball invariance inequality at the correction radius. -/
theorem ball_budget :
    eta⁻¹ * (residualBound + nonlinearBound * 63 ^ 2 * correctionRadius ^ 2) ≤
      correctionRadius := by
  norm_num [eta, residualBound, nonlinearBound, correctionRadius]

/-- Common coercivity margin after the moment-residual error. -/
theorem coercivity_budget :
    (29 / 100 : ℝ) < 109 / 350 - (164 / 25) * (3 / 2500) := by
  norm_num

/-- Endpoint error allowed by the largest of the three change-of-variable bounds. -/
theorem endpoint_budget :
    2 * nonlinearBound * targetError * 828 < (11 / 100 : ℝ) := by
  norm_num [nonlinearBound, targetError]

/-- The certified total matrix error is smaller than the certified spectral gap. -/
theorem matrix_budget :
    (151 / 50000 : ℝ) < 669 / 100000 ∧
      (669 / 100000 : ℝ) < eta / (eta + (164 / 25) * (164 / 25 + 3 / 2500)) := by
  norm_num [eta]

section Contraction

variable {E Y : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The actual quadratic fixed-point map from the stationary correction argument,
written for arbitrary Banach spaces. `I` is the modified inverse, `T = I+G₀`,
and `N` is the projected tensor-divergence bilinear map. -/
def correctionMap (I : Y →L[ℝ] E) (T : E →L[ℝ] E)
    (N : E →L[ℝ] E →L[ℝ] Y) (f : Y) (w : E) : E :=
  I (-f - N (T w) (T w))

/-- Bilinearity gives the quadratic difference identity, with no differential
or inverse-operator assumption. -/
theorem quadratic_difference (N : E →L[ℝ] E →L[ℝ] Y) (x y : E) :
    N x x - N y y = N (x - y) x + N y (x - y) := by
  simp only [map_sub, sub_apply]
  abel

/-- Norm estimate for the quadratic term, using its actual bilinear operator norm. -/
theorem quadratic_norm (N : E →L[ℝ] E →L[ℝ] Y) (T : E →L[ℝ] E)
    (hN : ‖N‖ ≤ nonlinearBound) (hT : ‖T‖ ≤ 63) (x : E) :
    ‖N (T x) (T x)‖ ≤ nonlinearBound * 63 ^ 2 * ‖x‖ ^ 2 := by
  have hx : ‖T x‖ ≤ 63 * ‖x‖ :=
    (T.le_opNorm x).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg x))
  have hN0 : 0 ≤ nonlinearBound := by norm_num [nonlinearBound]
  have h1 : ‖N (T x)‖ ≤ nonlinearBound * ‖T x‖ :=
    (N.le_opNorm (T x)).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg _))
  calc
    ‖N (T x) (T x)‖ ≤ ‖N (T x)‖ * ‖T x‖ := (N (T x)).le_opNorm _
    _ ≤ (nonlinearBound * ‖T x‖) * ‖T x‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ (nonlinearBound * (63 * ‖x‖)) * (63 * ‖x‖) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hx hN0) hx
        (norm_nonneg _) (by positivity)
    _ = nonlinearBound * 63 ^ 2 * ‖x‖ ^ 2 := by ring

/-- Lipschitz estimate for the quadratic term on a norm ball. -/
theorem quadratic_lipschitz (N : E →L[ℝ] E →L[ℝ] Y) (T : E →L[ℝ] E)
    (hN : ‖N‖ ≤ nonlinearBound) (hT : ‖T‖ ≤ 63)
    {x y : E} (hx : ‖x‖ ≤ correctionRadius) (hy : ‖y‖ ≤ correctionRadius) :
    ‖N (T x) (T x) - N (T y) (T y)‖ ≤
      2 * nonlinearBound * 63 ^ 2 * correctionRadius * ‖x - y‖ := by
  have hT' (w : E) : ‖T w‖ ≤ 63 * ‖w‖ :=
    (T.le_opNorm w).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg w))
  have hN' (u v : E) : ‖N u v‖ ≤ nonlinearBound * ‖u‖ * ‖v‖ := by
    calc
      ‖N u v‖ ≤ ‖N u‖ * ‖v‖ := (N u).le_opNorm v
      _ ≤ (‖N‖ * ‖u‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (N.le_opNorm u) (norm_nonneg v)
      _ ≤ nonlinearBound * ‖u‖ * ‖v‖ := by
        gcongr
  have hc : 0 ≤ nonlinearBound := by norm_num [nonlinearBound]
  have hr : 0 ≤ correctionRadius := by
    norm_num [correctionRadius, residualBound, eta]
  have hTx : ‖T x‖ ≤ 63 * correctionRadius := (hT' x).trans (by gcongr)
  have hTy : ‖T y‖ ≤ 63 * correctionRadius := (hT' y).trans (by gcongr)
  have hTd : ‖T x - T y‖ ≤ 63 * ‖x - y‖ := by
    simpa only [map_sub] using hT' (x - y)
  calc
    ‖N (T x) (T x) - N (T y) (T y)‖ =
        ‖N (T x - T y) (T x) + N (T y) (T x - T y)‖ := by
      rw [quadratic_difference]
    _ ≤ ‖N (T x - T y) (T x)‖ + ‖N (T y) (T x - T y)‖ := norm_add_le _ _
    _ ≤ nonlinearBound * ‖T x - T y‖ * ‖T x‖ +
        nonlinearBound * ‖T y‖ * ‖T x - T y‖ := add_le_add (hN' _ _) (hN' _ _)
    _ ≤ nonlinearBound * (63 * ‖x - y‖) * (63 * correctionRadius) +
        nonlinearBound * (63 * correctionRadius) * (63 * ‖x - y‖) := by
      gcongr
    _ = 2 * nonlinearBound * 63 ^ 2 * correctionRadius * ‖x - y‖ := by ring

/-- The stationary correction exists under explicit inverse and bilinear operator bounds. -/
theorem stationary_contraction [CompleteSpace E] (I : Y →L[ℝ] E) (T : E →L[ℝ] E)
    (N : E →L[ℝ] E →L[ℝ] Y) (f : Y)
    (hI : ‖I‖ ≤ eta⁻¹) (hT : ‖T‖ ≤ 63) (hN : ‖N‖ ≤ nonlinearBound)
    (hf : ‖f‖ ≤ residualBound) :
    ∃ w : E, ‖w‖ ≤ correctionRadius ∧
      correctionMap I T N f w = w ∧ ‖T w‖ < targetError := by
  have hr : 0 ≤ correctionRadius := by
    norm_num [correctionRadius, residualBound, eta]
  have hη : 0 ≤ eta⁻¹ := by norm_num [eta]
  have hc : 0 ≤ nonlinearBound := by norm_num [nonlinearBound]
  let Φ : E → E := correctionMap I T N f
  have hmaps : Set.MapsTo Φ (Metric.closedBall 0 correctionRadius)
      (Metric.closedBall 0 correctionRadius) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    calc
      ‖Φ x‖ ≤ ‖I‖ * ‖-f - N (T x) (T x)‖ := I.le_opNorm _
      _ ≤ eta⁻¹ * ‖-f - N (T x) (T x)‖ := by gcongr
      _ ≤ eta⁻¹ * (‖f‖ + ‖N (T x) (T x)‖) := by
        gcongr
        simpa only [norm_neg] using norm_sub_le (-f) (N (T x) (T x))
      _ ≤ eta⁻¹ * (residualBound + nonlinearBound * 63 ^ 2 * ‖x‖ ^ 2) := by
        gcongr
        exact quadratic_norm N T hN hT x
      _ ≤ eta⁻¹ * (residualBound + nonlinearBound * 63 ^ 2 * correctionRadius ^ 2) := by
        gcongr
      _ ≤ correctionRadius := ball_budget
  have hcon : ContractingWith (27 / 1000)
      (hmaps.restrict Φ (Metric.closedBall 0 correctionRadius)
        (Metric.closedBall 0 correctionRadius)) := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      have hx : ‖(x : E)‖ ≤ correctionRadius := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
      have hy : ‖(y : E)‖ ≤ correctionRadius := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using y.property
      change dist (Φ x) (Φ y) ≤ ((27 / 1000 : NNReal) : ℝ) * dist (x : E) (y : E)
      rw [dist_eq_norm, dist_eq_norm]
      have hdiff : Φ x - Φ y =
          I (-(N (T (x : E)) (T (x : E)) - N (T (y : E)) (T (y : E)))) := by
        change I _ - I _ = I _
        rw [← map_sub]
        congr 1
        abel
      rw [hdiff]
      calc
        ‖I (-(N (T (x : E)) (T (x : E)) - N (T (y : E)) (T (y : E))))‖ ≤
            eta⁻¹ * ‖N (T (x : E)) (T (x : E)) - N (T (y : E)) (T (y : E))‖ := by
          simpa only [norm_neg] using
            (I.le_opNorm (-(N (T (x : E)) (T (x : E)) - N (T (y : E)) (T (y : E))))).trans
              (mul_le_mul_of_nonneg_right hI (norm_nonneg _))
        _ ≤ eta⁻¹ * (2 * nonlinearBound * 63 ^ 2 * correctionRadius *
            ‖(x : E) - (y : E)‖) :=
          mul_le_mul_of_nonneg_left (quadratic_lipschitz N T hN hT hx hy) hη
        _ = (2 * nonlinearBound * 63 ^ 2 * correctionRadius / eta) *
            ‖(x : E) - (y : E)‖ := by ring
        _ ≤ ((27 / 1000 : NNReal) : ℝ) * ‖(x : E) - (y : E)‖ := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_of_lt lipschitz_budget)
            (norm_nonneg _)
  obtain ⟨w, hw, hfix, _⟩ := hcon.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hmaps
    (x := (0 : E)) (by simpa only [Metric.mem_closedBall, dist_self] using hr)
    (edist_ne_top _ _)
  have hw' : ‖w‖ ≤ correctionRadius := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  refine ⟨w, hw', hfix, ?_⟩
  calc
    ‖T w‖ ≤ ‖T‖ * ‖w‖ := T.le_opNorm w
    _ ≤ 63 * correctionRadius := by gcongr
    _ < targetError := correction_budget

end Contraction

end StationaryNS

end

end OAI
