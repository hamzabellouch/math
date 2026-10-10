import Mathlib
import OAI.Analysis.AffineBernstein.SupportAnnulus
import OAI.Analysis.AffineBernstein.SupportRadial

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open scoped Matrix

variable {n : ℕ}

/- The full cofactor trace is the genuine Euclidean angular area density of
its smooth support function. Its spherical integral is bounded solely by the
radius of the compact convex fiber. No surface-area estimate is assumed. -/
theorem sphere_support_cofactor_le_ball {K : Set (Space n)} (hn : 1 ≤ n)
    (hK : IsCompact K) (hne : K.Nonempty)
    (hH : ∀ x : Space n, x ≠ 0 → ContDiffAt ℝ ∞ (homogeneousSupport K) x)
    {R : ℝ} (hR : ∀ y ∈ K, ‖y‖ ≤ R) :
    (∫⁻ e : Metric.sphere (0:Space n) 1,
      ENNReal.ofReal (hessian (homogeneousSupport K) e).adjugate.trace ∂volume.toSphere) ≤
      (n:ℝ≥0∞)^2 * volume (Metric.closedBall (0:Space n) (R+1)) := by
  let f : Space n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (hessian (homogeneousSupport K) x).adjugate.trace
  have he (e : Metric.sphere (0:Space n) 1) : (e:Space n) ≠ 0 :=
    Metric.ne_of_mem_sphere e.property one_ne_zero
  have hh : Continuous (fun e : Metric.sphere (0:Space n) 1 =>
      hessian (homogeneousSupport K) (e:Space n)) := by
    apply continuous_iff_continuousAt.mpr
    intro e
    exact (continuousAt_hessian (hH e (he e))).comp continuous_subtype_val.continuousAt
  have hf : Measurable (fun e : Metric.sphere (0:Space n) 1 => f e) :=
    (ENNReal.continuous_ofReal.comp hh.matrix_adjugate.matrix_trace).measurable
  have hpolar := sphere_lintegral_mul_radial_le (volume : Measure (Space n)) hf
    (fun e r hr hr1 => support_cofactor_radial_expansion hK hne hH (he e) hr hr1.le)
  have hdim : Module.finrank ℝ (Space n) - 1 + 1 = n := by
    rw [finrank_euclideanSpace,Fintype.card_fin]
    omega
  rw [hdim] at hpolar
  have hvol := lintegral_support_cofactor_le_ball (n := n) (R := R) (r := 1)
    (D := Metric.ball (0:Space n) 1 \ {0}) hK hne
    (measurableSet_ball.diff (measurableSet_singleton 0))
    (fun x hx => hH x hx.2) hR
    (fun x hx => le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hx.1))
  have hbound : (∫⁻ e : Metric.sphere (0:Space n) 1, f e ∂volume.toSphere) *
      ENNReal.ofReal (1 / (n:ℝ)) ≤
      (n:ℝ≥0∞)*volume (Metric.closedBall (0:Space n) (R+1)) := hpolar.trans hvol
  have hcancel : ENNReal.ofReal (1 / (n:ℝ)) * (n:ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),
      one_div_mul_cancel (show (n:ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn),
      ENNReal.ofReal_one]
  calc
    _ = ((∫⁻ e : Metric.sphere (0:Space n) 1, f e ∂volume.toSphere) *
        ENNReal.ofReal (1 / (n:ℝ))) * (n:ℝ≥0∞) := by rw [mul_assoc,hcancel,mul_one]
    _ ≤ ((n:ℝ≥0∞)*volume (Metric.closedBall (0:Space n) (R+1)))*(n:ℝ≥0∞) :=
      mul_le_mul' hbound le_rfl
    _ = _ := by ring

end AffineBernstein
end

end OAI
