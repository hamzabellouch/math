import OAI.Geometry.RCD.Sobolev.DyadicTailBound
import OAI.Geometry.RCD.Sobolev.UniformAnnularCoercivity
import OAI.Geometry.RCD.Sobolev.GeometricTailMoment
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OAI

/-! # A superquadratic moment for normalized Dirichlet functions -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The dyadic support estimate improves the exponent above two.
Only the annulus, bounded rescaled curvature, and unit energy normalization
are needed; all constants precede the center and radius. -/
theorem NoncollapsedRCD.normalized_dirichlet_moment {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ p C : ℝ, 2 < p ∧ 0 < C ∧ ∀ (x : X) (R : ℝ), 0 < R → -1 ≤ K*(2*R)^2 →
      2*(hausdorff n X).real (ball x R) ≤ (hausdorff n X).real (ball x (2*R)) →
      ∀ w : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball x R),
      R^2*energyForm (hausdorff n X) hX.quadratic w.val w.val ≤
        (hausdorff n X).real (ball x R) →
      IntegrableOn (fun y => |SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val y|^p)
        (ball x R) (hausdorff n X) ∧
      (∫ y in ball x R, |SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val y|^p
        ∂hausdorff n X) ≤ C*(hausdorff n X).real (ball x R) := by
  obtain ⟨C₀, D, hC₀, hD, htail⟩ := hX.dyadic_tail_bound hn
  obtain ⟨P, hP, hPoincare⟩ := hX.uniform_annular_coercivity hn
  let b := Real.sqrt D
  have hDpos : 0 < D := by linarith
  have hb0 : 0 < b := Real.sqrt_pos.mpr hDpos
  have hb2 : b^2 = D := Real.sq_sqrt hDpos.le
  have hb : 1 < b := by nlinarith
  let p := 2 + Real.logb b 2
  have hp : 2 < p := by
    have hl : 0 < Real.logb b 2 := by
      unfold Real.logb
      exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos hb)
    dsimp only [p]
    linarith
  have hp0 : 0 < p := by linarith
  have hbpow : b^p = 2*D := by
    dsimp only [p]
    rw [Real.rpow_add hb0, Real.rpow_two,
      Real.rpow_logb hb0 (ne_of_gt hb) (by norm_num), hb2]
    ring
  let σ := Real.sqrt (2*D*P)
  have hσ : 0 < σ := Real.sqrt_pos.mpr (by positivity)
  have hσ2 : σ^2 = 2*D*P := Real.sq_sqrt (by positivity)
  let S := 2*σ
  let q := 1/(4*D)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hdecay : b^p*q = 1/2 := by rw [hbpow]; dsimp only [q]; field_simp; ring
  let C := (S*b)^p + 2*(C₀/σ^2)*(S*b^2)^p
  have hC : 0 < C := by
    have ha : 0 < (S*b)^p := Real.rpow_pos_of_pos (by dsimp only [S]; positivity) _
    have hh : 0 < 2*(C₀/σ^2)*(S*b^2)^p := by positivity
    exact add_pos ha hh
  refine ⟨p, C, hp, hC, ?_⟩
  intro x R hR hcurv hann w hnorm
  let μ := hausdorff n X
  let u := SobolevSpace.toLp μ hX.quadratic w.val
  let V := μ.real (ball x R)
  let E := energyForm μ hX.quadratic w.val w.val
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport x R hR).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hE : 0 ≤ E := by
    dsimp only [E]
    rw [energyForm_self]
    exact mul_nonneg (by norm_num) (SobolevSpace.energy_nonneg μ hX.quadratic w.val)
  have hnorm' : R^2*E ≤ V := hnorm
  have hl2 : ‖u‖^2 ≤ P*V := by
    have hh := hPoincare x R hR hcurv hann w
    have hm := mul_le_mul_of_nonneg_left hnorm' hP.le
    change ‖u‖^2 ≤ P*R^2*E at hh
    nlinarith
  have hcurvR : -1 ≤ K*R^2 := by
    by_cases hK : 0 ≤ K
    · exact (by norm_num : (-1:ℝ)≤0).trans (mul_nonneg hK (sq_nonneg R))
    · have hh := mul_le_mul_of_nonpos_left (show R^2 ≤ (2*R)^2 by nlinarith)
        (le_of_not_ge hK)
      linarith
  have ht2 (k : ℕ) : (σ*b^k)^2 = (2*D*P)*D^k := by
    rw [mul_pow, hσ2, ← pow_mul, Nat.mul_comm k 2, pow_mul, hb2]
  have hfour (k : ℕ) : ((2:ℝ)^k)^2 = (4:ℝ)^k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  have hlevels (k : ℕ) : (μ.restrict (ball x R)).real {y | S*b^k < |u y|} ≤
      ((C₀/σ^2)*V)*q^k := by
    let t := σ*b^k
    have ht : 0 < t := mul_pos hσ (pow_pos hb0 _)
    have hparam : 2*D^(k+1)*‖u‖^2 ≤ V*t^2 := by
      calc
        _ ≤ 2*D^(k+1)*(P*V) := mul_le_mul_of_nonneg_left hl2 (by positivity)
        _ = _ := by dsimp only [t]; rw [ht2, pow_succ]; ring
    have hh := htail x R hR hcurvR w t ht k hparam
    change t^2 * μ.real (ball x R ∩ {y | 2*t < |u y|}) ≤ C₀*(R/2^k)^2*E at hh
    have hparam' : C₀*(R/2^k)^2*E ≤ C₀*V/(4:ℝ)^k := by
      rw [div_pow, hfour]
      have hmul := mul_le_mul_of_nonneg_left hnorm' hC₀.le
      apply (le_div_iff₀ (pow_pos (by norm_num : (0:ℝ)<4) k)).mpr
      field_simp at *
      nlinarith
    have halg : t^2 * (((C₀/σ^2)*V)*q^k) = C₀*V/(4:ℝ)^k := by
      dsimp only [t, q]
      rw [ht2, hσ2, div_pow, one_pow, mul_pow]
      field_simp
    have hmeasure : μ.real (ball x R ∩ {y | 2*t < |u y|}) ≤ ((C₀/σ^2)*V)*q^k := by
      apply (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp
      rw [halg]
      exact hh.trans hparam'
    rw [measureReal_restrict_apply (measurableSet_lt measurable_const
      (Lp.stronglyMeasurable u).measurable.abs)]
    simpa only [S, t, mul_assoc, inter_comm] using hmeasure
  let : IsFiniteMeasure (μ.restrict (ball x R)) :=
    ⟨by simpa using hX.finiteOnBounded (ball x R) isBounded_ball⟩
  obtain ⟨hi, hbnd⟩ := geometric_tail_moment (μ.restrict (ball x R))
    (Lp.stronglyMeasurable u).measurable.abs (fun _ => abs_nonneg _)
    (show 0 < S by dsimp only [S]; positivity) hb
    (show 0 ≤ (C₀/σ^2)*V by positivity) hq.le hp0
    (by rw [hdecay]; norm_num) hlevels
  refine ⟨hi, ?_⟩
  have hunit : (μ.restrict (ball x R)).real univ = V := by
    simp only [Measure.real, Measure.restrict_apply_univ, V]
  rw [hunit, hdecay] at hbnd
  calc
    _ ≤ (S*b)^p*V + ((C₀/σ^2)*V)*(S*b^2)^p/(1-1/2) := hbnd
    _ = C*V := by dsimp only [C]; ring

end RegularPointCoordinates

end

end OAI
