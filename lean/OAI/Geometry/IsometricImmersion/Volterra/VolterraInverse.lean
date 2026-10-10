import OAI.Geometry.IsometricImmersion.Volterra.VolterraOperator
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section
open scoped ContDiff Topology

namespace SmoothLocal.ODE

def curvatureVolterraCLM (r : ℝ) (hr : 0 < r) (k : IntervalFunctions r) :
    IntervalFunctions r →L[ℝ] IntervalFunctions r :=
  (volterraCLM r hr).comp (ContinuousLinearMap.mul ℝ (IntervalFunctions r) k)

theorem curvatureVolterraCLM_norm_le (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) : ‖curvatureVolterraCLM r hr k‖ ≤ ‖k‖ := by
  calc
    ‖curvatureVolterraCLM r hr k‖ ≤
        ‖volterraCLM r hr‖ * ‖ContinuousLinearMap.mul ℝ (IntervalFunctions r) k‖ :=
      (volterraCLM r hr).opNorm_comp_le _
    _ ≤ 1 * ‖k‖ := mul_le_mul (volterraCLM_norm_le_one r hr hr1)
      (ContinuousLinearMap.opNorm_mul_apply_le ℝ (IntervalFunctions r) k)
      (norm_nonneg _) zero_le_one
    _ = ‖k‖ := one_mul _

theorem curvatureVolterraCLM_contDiff (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ ∞ (curvatureVolterraCLM r hr) := by
  have hmul : ContDiff ℝ ∞ (ContinuousLinearMap.mul ℝ (IntervalFunctions r)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (E := IntervalFunctions r) (F := IntervalFunctions r →L[ℝ] IntervalFunctions r)
      (ContinuousLinearMap.mul ℝ (IntervalFunctions r))
  exact (contDiff_const : ContDiff ℝ ∞
    (fun _ : IntervalFunctions r => volterraCLM r hr)).clm_comp hmul

theorem one_add_curvatureVolterra_isUnit (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) :
    IsUnit (1 + curvatureVolterraCLM r hr k) := by
  have hT : ‖curvatureVolterraCLM r hr k‖ < 1 :=
    lt_of_le_of_lt ((curvatureVolterraCLM_norm_le r hr hr1 k).trans hk) (by norm_num)
  have hneg : ‖-curvatureVolterraCLM r hr k‖ < 1 := by
    rw [ContinuousLinearMap.opNorm_neg]
    exact hT
  simpa only [sub_neg_eq_add] using
    (isUnit_one_sub_of_norm_lt_one
      (R := IntervalFunctions r →L[ℝ] IntervalFunctions r)
      (x := -curvatureVolterraCLM r hr k) hneg)

def volterraSolution (r : ℝ) (hr : 0 < r) (k : IntervalFunctions r) : IntervalFunctions r :=
  Ring.inverse (1 + curvatureVolterraCLM r hr k) 1

theorem volterraSolution_equation (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) :
    volterraSolution r hr k + volterraCLM r hr (k * volterraSolution r hr k) = 1 := by
  have hunit := one_add_curvatureVolterra_isUnit r hr hr1 k hk
  have he := congrArg (fun L : IntervalFunctions r →L[ℝ] IntervalFunctions r => L 1)
    (Ring.mul_inverse_cancel (1 + curvatureVolterraCLM r hr k) hunit)
  change volterraSolution r hr k +
    volterraCLM r hr (k * volterraSolution r hr k) = 1 at he
  exact he

theorem volterraSolution_unique (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000)
    (f : IntervalFunctions r) (hf : f + volterraCLM r hr (k * f) = 1) :
    f = volterraSolution r hr k := by
  have hunit := one_add_curvatureVolterra_isUnit r hr hr1 k hk
  have hAf : (1 + curvatureVolterraCLM r hr k) f = 1 := hf
  have he := congrArg (fun L : IntervalFunctions r →L[ℝ] IntervalFunctions r => L f)
    (Ring.inverse_mul_cancel (1 + curvatureVolterraCLM r hr k) hunit)
  change Ring.inverse (1 + curvatureVolterraCLM r hr k)
    ((1 + curvatureVolterraCLM r hr k) f) = f at he
  rw [hAf] at he
  exact he.symm

theorem volterraSolution_contDiffAt (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) :
    ContDiffAt ℝ ∞ (volterraSolution r hr) k := by
  obtain ⟨u, hu⟩ := one_add_curvatureVolterra_isUnit r hr hr1 k hk
  have hinv : ContDiffAt ℝ ∞
      (Ring.inverse : (IntervalFunctions r →L[ℝ] IntervalFunctions r) →
        (IntervalFunctions r →L[ℝ] IntervalFunctions r))
      (1 + curvatureVolterraCLM r hr k) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ
      (R := IntervalFunctions r →L[ℝ] IntervalFunctions r) (n := ∞) u
  have harg : ContDiffAt ℝ ∞
      (fun q : IntervalFunctions r => 1 + curvatureVolterraCLM r hr q) k :=
    contDiffAt_const.add (curvatureVolterraCLM_contDiff r hr).contDiffAt
  exact (hinv.comp k harg).clm_apply contDiffAt_const

theorem volterraSolution_family_contDiffOn
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    {s : Set P} {K : P → IntervalFunctions r}
    (hK : ContDiffOn ℝ ∞ K s)
    (hbound : ∀ y ∈ s, ‖K y‖ ≤ (1 : ℝ) / 1000) :
    ContDiffOn ℝ ∞ (fun y => volterraSolution r hr (K y)) s := by
  intro y hy
  exact (volterraSolution_contDiffAt r hr hr1 (K y) (hbound y hy)).comp_contDiffWithinAt
    y (hK y hy)

end SmoothLocal.ODE

end

end OAI
