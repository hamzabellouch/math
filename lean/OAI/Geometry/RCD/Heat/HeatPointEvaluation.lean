import OAI.Geometry.RCD.Heat.HeatLocalSmoothing
import OAI.Geometry.RCD.Heat.BoundedHeatIntegral

namespace OAI

/-! # Pointwise L² control of bounded heat evaluations

Full support promotes the local almost-everywhere smoothing estimate to
all points of the continuous bounded-data representative.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A radius below both the time and curvature scales. -/
theorem exists_heat_local_radius (K t : ℝ) (ht : 0 < t) :
    ∃ R : ℝ, 0 < R ∧ R^2 < t ∧ -1 ≤ K*R^2 := by
  let R := min (Real.sqrt (t/2)) (Real.sqrt (1/(|K|+1)))
  have ht2 : 0 < t/2 := half_pos ht
  have hk : 0 < 1/(|K|+1) := by positivity
  have hR : 0 < R := lt_min (Real.sqrt_pos.mpr ht2) (Real.sqrt_pos.mpr hk)
  have hRt : R^2 ≤ t/2 := by
    have hh := (sq_le_sq₀ hR.le (Real.sqrt_nonneg (t/2))).mpr (min_le_left _ _)
    simpa only [Real.sq_sqrt ht2.le] using hh
  have hRK : R^2 ≤ 1/(|K|+1) := by
    have hh := (sq_le_sq₀ hR.le (Real.sqrt_nonneg (1/(|K|+1)))).mpr (min_le_right _ _)
    simpa only [Real.sq_sqrt hk.le] using hh
  have hmul : (|K|+1)*R^2 ≤ 1 := by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < |K|+1)).mp hRK
  have hlo := neg_abs_le K
  refine ⟨R,hR,by linarith,?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hlo (sq_nonneg R)]

namespace NoncollapsedRCD
variable {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X)
  [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem boundedHeat_local_L2_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x : X) (R t : ℝ) (_hR : 0 < R)
      (_hcurv : -1 ≤ K*R^2) (hRt : R^2 < t),
      ∀ (f : Lp ℝ 2 (hausdorff n X)) (hf : HasBoundedAmplitude f),
      ∀ y ∈ ball x (R/2), |hX.boundedHeat hn p f hf t (lt_of_le_of_lt (sq_nonneg R) hRt) y| ≤
        C/Real.sqrt ((hausdorff n X).real (ball x R))*‖f‖ := by
  obtain ⟨C,hC,hbound⟩ := hX.heat_local_L2_smoothing hn
  refine ⟨C,hC,?_⟩
  intro x R t hR hcurv hRt f hf y hy
  have ht : 0 < t := lt_of_le_of_lt (sq_nonneg R) hRt
  let := hX.openPos K n
  have hb := hbound x R (t-R^2) hR hcurv (sub_pos.mpr hRt) f
  have he : t-R^2+R^2 = t := by ring
  rw [he] at hb
  have hae : (fun z => min |hX.boundedHeat hn p f hf t ht z|
      (C/Real.sqrt ((hausdorff n X).real (ball x R))*‖f‖)) =ᵐ[(hausdorff n X).restrict (ball x (R/2))]
      (fun z => |hX.boundedHeat hn p f hf t ht z|) := by
    filter_upwards [hb,ae_restrict_of_ae (hX.boundedHeat_represents hn p f hf t ht)] with z hz he
    exact min_eq_left (by simpa only [he] using hz)
  have hc := (hX.boundedHeat_continuous hn p f hf t ht).abs
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_ball
    (hc.min continuous_const).continuousOn hc.continuousOn
  exact min_eq_left_iff.mp (heq hy)

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
/-- At every positive time, a common radius gives locally uniform bounded
linear evaluations on bounded L² data. -/
theorem boundedHeat_L2_evaluation (t : ℝ) (ht : 0 < t) :
    ∃ R C : ℝ, 0 < R ∧ 1 ≤ C ∧ ∀ (x : X)
      (f : Lp ℝ 2 (hausdorff n X)) (hf : HasBoundedAmplitude f),
      |hX.boundedHeat hn p f hf t ht x| ≤
        C/Real.sqrt ((hausdorff n X).real (ball x R))*‖f‖ := by
  obtain ⟨R,hR,hRt,hcurv⟩ := exists_heat_local_radius K t ht
  obtain ⟨C,hC,hbound⟩ := hX.boundedHeat_local_L2_bound hn p
  exact ⟨R,C,hR,hC,fun x f hf => hbound x R t hR hcurv hRt f hf x (mem_ball_self (half_pos hR))⟩

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
