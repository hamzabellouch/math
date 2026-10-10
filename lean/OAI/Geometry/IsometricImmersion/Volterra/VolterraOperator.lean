import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology Interval

namespace SmoothLocal.ODE

abbrev IntervalFunctions (r : ℝ) := C(Icc (-r) r, ℝ)

def intervalExtension (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) : C(ℝ, ℝ) :=
  letI : Fact (-r ≤ r) := ⟨by linarith⟩
  ContinuousMap.IccExtendCM h

theorem intervalExtension_apply_of_mem (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) {x : ℝ} (hx : x ∈ Icc (-r) r) :
    intervalExtension r hr h x = h ⟨x, hx⟩ := by
  let : Fact (-r ≤ r) := ⟨by linarith⟩
  exact ContinuousMap.IccExtendCM_of_mem hx

theorem intervalExtension_norm_le (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : ℝ) :
    ‖intervalExtension r hr h x‖ ≤ ‖h‖ := by
  exact h.norm_coe_le_norm _

@[simp]
theorem intervalExtension_add (r : ℝ) (hr : 0 < r)
    (h k : IntervalFunctions r) (x : ℝ) :
    intervalExtension r hr (h + k) x =
      intervalExtension r hr h x + intervalExtension r hr k x := rfl

@[simp]
theorem intervalExtension_smul (r : ℝ) (hr : 0 < r)
    (c : ℝ) (h : IntervalFunctions r) (x : ℝ) :
    intervalExtension r hr (c • h) x = c • intervalExtension r hr h x := rfl

def primitiveFunction (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) (x : ℝ) : ℝ :=
  ∫ t in 0..x, intervalExtension r hr h t

theorem primitiveFunction_continuous (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) : Continuous (primitiveFunction r hr h) :=
  (intervalIntegral.differentiable_integral_of_continuous
    (intervalExtension r hr h).continuous).continuous

theorem primitiveFunction_hasDerivAt (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : ℝ) :
    HasDerivAt (primitiveFunction r hr h) (intervalExtension r hr h x) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((intervalExtension r hr h).continuous.intervalIntegrable 0 x)
    ((intervalExtension r hr h).continuous.stronglyMeasurableAtFilter volume (𝓝 x))
    (intervalExtension r hr h).continuous.continuousAt

def primitiveMap (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) : IntervalFunctions r :=
  ⟨fun x => primitiveFunction r hr h x,
    (primitiveFunction_continuous r hr h).comp continuous_subtype_val⟩

@[simp]
theorem primitiveMap_apply (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : Icc (-r) r) :
    primitiveMap r hr h x = ∫ t in 0..(x : ℝ), intervalExtension r hr h t := rfl

def primitiveLinearMap (r : ℝ) (hr : 0 < r) :
    IntervalFunctions r →ₗ[ℝ] IntervalFunctions r where
  toFun := primitiveMap r hr
  map_add' h k := by
    apply ContinuousMap.ext
    intro x
    change (∫ t in 0..(x : ℝ), intervalExtension r hr (h + k) t) =
      (∫ t in 0..(x : ℝ), intervalExtension r hr h t) +
      (∫ t in 0..(x : ℝ), intervalExtension r hr k t)
    simp only [intervalExtension_add]
    exact intervalIntegral.integral_add
      ((intervalExtension r hr h).continuous.intervalIntegrable 0 x)
      ((intervalExtension r hr k).continuous.intervalIntegrable 0 x)
  map_smul' c h := by
    apply ContinuousMap.ext
    intro x
    change (∫ t in 0..(x : ℝ), intervalExtension r hr (c • h) t) =
      c • (∫ t in 0..(x : ℝ), intervalExtension r hr h t)
    simp only [intervalExtension_smul]
    exact intervalIntegral.integral_smul c (fun t => intervalExtension r hr h t)

theorem primitiveMap_norm_le (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) :
    ‖primitiveMap r hr h‖ ≤ r * ‖h‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hr.le (norm_nonneg h))).mpr
  intro x
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (x : ℝ)) (C := ‖h‖)
    (f := fun t => intervalExtension r hr h t)
    (fun t _ => intervalExtension_norm_le r hr h t)
  have hx : |(x : ℝ)| ≤ r := abs_le.mpr x.2
  change ‖∫ t in 0..(x : ℝ), intervalExtension r hr h t‖ ≤ r * ‖h‖
  calc
    ‖∫ t in 0..(x : ℝ), intervalExtension r hr h t‖ ≤ ‖h‖ * |(x : ℝ)| := by
      simpa only [sub_zero] using hi
    _ ≤ ‖h‖ * r := mul_le_mul_of_nonneg_left hx (norm_nonneg h)
    _ = r * ‖h‖ := mul_comm _ _

def primitiveCLM (r : ℝ) (hr : 0 < r) :
    IntervalFunctions r →L[ℝ] IntervalFunctions r :=
  (primitiveLinearMap r hr).mkContinuous r (primitiveMap_norm_le r hr)

@[simp]
theorem primitiveCLM_apply (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : Icc (-r) r) :
    primitiveCLM r hr h x = ∫ t in 0..(x : ℝ), intervalExtension r hr h t := rfl

theorem primitiveCLM_norm_le (r : ℝ) (hr : 0 < r) :
    ‖primitiveCLM r hr‖ ≤ r :=
  LinearMap.mkContinuous_norm_le (primitiveLinearMap r hr) hr.le (primitiveMap_norm_le r hr)

def volterraCLM (r : ℝ) (hr : 0 < r) :
    IntervalFunctions r →L[ℝ] IntervalFunctions r :=
  (primitiveCLM r hr).comp (primitiveCLM r hr)

theorem volterraCLM_apply (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : Icc (-r) r) :
    volterraCLM r hr h x =
      ∫ s in 0..(x : ℝ), ∫ t in 0..s, intervalExtension r hr h t := by
  change (∫ s in 0..(x : ℝ), intervalExtension r hr (primitiveCLM r hr h) s) = _
  apply intervalIntegral.integral_congr
  intro s hs
  have hz : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  have hsmem : s ∈ Icc (-r) r := uIcc_subset_Icc hz x.2 hs
  rw [intervalExtension_apply_of_mem r hr (primitiveCLM r hr h) hsmem]
  rfl

theorem volterraCLM_norm_le (r : ℝ) (hr : 0 < r) : ‖volterraCLM r hr‖ ≤ r ^ 2 := by
  calc
    ‖volterraCLM r hr‖ ≤ ‖primitiveCLM r hr‖ * ‖primitiveCLM r hr‖ :=
      (primitiveCLM r hr).opNorm_comp_le (primitiveCLM r hr)
    _ ≤ r * r := mul_le_mul (primitiveCLM_norm_le r hr) (primitiveCLM_norm_le r hr)
      (ContinuousLinearMap.opNorm_nonneg _) hr.le
    _ = r ^ 2 := (pow_two r).symm

theorem volterraCLM_norm_le_one (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖volterraCLM r hr‖ ≤ 1 := by
  have hh := volterraCLM_norm_le r hr
  have hrr : r * r ≤ 1 * 1 := mul_le_mul hr1 hr1 hr.le zero_le_one
  nlinarith

end SmoothLocal.ODE

end

end OAI
