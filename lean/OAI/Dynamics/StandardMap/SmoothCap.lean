import OAI.Dynamics.StandardMap.ScaleTruncation

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Interval Topology
namespace StandardMapEntropy
noncomputable def capSlope (u : ℝ) : ℝ := 1-Real.smoothTransition (10000*u-1)
noncomputable def capPrimitive (u : ℝ) : ℝ := ∫ t in (0:ℝ)..u,capSlope t
noncomputable def capBase : ℝ := capPrimitive (1/5000)
noncomputable def entropyCap (α u : ℝ) : ℝ :=
  α*capPrimitive u+(1-α*capBase)*Real.smoothTransition (10000*u-2)
lemma capSlope_contDiff : ContDiff ℝ 2 capSlope := by unfold capSlope; fun_prop
lemma capSlope_continuous : Continuous capSlope := capSlope_contDiff.continuous
lemma capSlope_bounds (u : ℝ) : 0≤ capSlope u ∧ capSlope u≤1 := by
  unfold capSlope
  constructor <;> linarith [Real.smoothTransition.le_one (10000*u-1),Real.smoothTransition.nonneg (10000*u-1)]
lemma capSlope_one {u : ℝ} (hu : u≤1/10000) : capSlope u=1 := by
  unfold capSlope
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; ring
lemma capSlope_zero {u : ℝ} (hu : 1/5000≤ u) : capSlope u=0 := by
  unfold capSlope
  rw [Real.smoothTransition.one_of_one_le (by linarith)]; ring
lemma capPrimitive_hasDerivAt (u : ℝ) : HasDerivAt capPrimitive (capSlope u) u := by
  exact intervalIntegral.integral_hasDerivAt_right (capSlope_continuous.intervalIntegrable 0 u)
    (capSlope_continuous.stronglyMeasurableAtFilter volume (𝓝 u)) capSlope_continuous.continuousAt
lemma capPrimitive_deriv : deriv capPrimitive=capSlope := funext (fun u => (capPrimitive_hasDerivAt u).deriv)
lemma capPrimitive_contDiff : ContDiff ℝ 2 capPrimitive := by
  suffices ContDiff ℝ ((1 : WithTop ℕ∞)+1) capPrimitive by (convert this using 1; norm_num)
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun u => (capPrimitive_hasDerivAt u).differentiableAt,?_,?_⟩
  · norm_num
  · rw [capPrimitive_deriv]
    exact capSlope_contDiff.of_le (by norm_num)
lemma capPrimitive_monotone : Monotone capPrimitive := by
  intro x y hxy
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (capSlope_continuous.intervalIntegrable 0 x) (capSlope_continuous.intervalIntegrable x y)
  have h0 := intervalIntegral.integral_nonneg (μ := volume) hxy (fun t _ => (capSlope_bounds t).1)
  change (∫ t in (0:ℝ)..x,capSlope t)≤(∫ t in (0:ℝ)..y,capSlope t)
  linarith
lemma capPrimitive_linear {u : ℝ} (hu : u≤1/10000) : capPrimitive u=u := by
  unfold capPrimitive
  have he : (∫ t in (0:ℝ)..u,capSlope t)=(∫ _t in (0:ℝ)..u,(1:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply capSlope_one
    rw [mem_uIcc] at ht
    rcases ht with ⟨h0,h1⟩|⟨h0,h1⟩ <;> linarith
  rw [he,intervalIntegral.integral_const]
  simp
lemma capPrimitive_constant {u : ℝ} (hu : 1/5000≤ u) : capPrimitive u=capBase := by
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (capSlope_continuous.intervalIntegrable 0 (1/5000)) (capSlope_continuous.intervalIntegrable (1/5000) u)
  have hzero : (∫ t in (1/5000:ℝ)..u,capSlope t)=0 := by
    calc
      (∫ t in (1/5000:ℝ)..u,capSlope t)=(∫ _t in (1/5000:ℝ)..u,(0:ℝ)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact capSlope_zero (by rw [uIcc_of_le hu] at ht; exact ht.1)
      _=0 := by simp
  rw [hzero,add_zero] at he
  exact he.symm
lemma capBase_bounds : (1/10000:ℝ)≤ capBase ∧ capBase≤1/5000 := by
  constructor
  · have hh := capPrimitive_monotone (by norm_num : (1/10000:ℝ)≤1/5000)
    rwa [capPrimitive_linear (by norm_num : (1/10000:ℝ)≤1/10000)] at hh
  · unfold capBase capPrimitive
    calc
      (∫ t in (0:ℝ)..(1/5000:ℝ),capSlope t)≤∫ _t in (0:ℝ)..(1/5000:ℝ),(1:ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num) (capSlope_continuous.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        exact fun t _ => (capSlope_bounds t).2
      _=1/5000 := by simp
lemma entropyCap_contDiff (α : ℝ) : ContDiff ℝ 2 (entropyCap α) := by
  unfold entropyCap
  exact (contDiff_const.mul capPrimitive_contDiff).add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)))
lemma entropyCap_linear {α u : ℝ} (hu : u≤1/10000) : entropyCap α u=α*u := by
  unfold entropyCap
  rw [capPrimitive_linear hu,Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring
lemma entropyCap_one {α u : ℝ} (hu : 3/10000≤ u) : entropyCap α u=1 := by
  unfold entropyCap
  rw [capPrimitive_constant (by linarith),Real.smoothTransition.one_of_one_le (by linarith)]
  ring
lemma entropyCap_monotone {α : ℝ} (hα : 0≤α) (hα1 : α≤1) : Monotone (entropyCap α) := by
  have hc : 0≤1-α*capBase := by nlinarith [capBase_bounds.1,capBase_bounds.2]
  intro x y hxy
  unfold entropyCap
  exact add_le_add (mul_le_mul_of_nonneg_left (capPrimitive_monotone hxy) hα)
    (mul_le_mul_of_nonneg_left (Real.smoothTransition.monotone (by linarith)) hc)
lemma entropyCap_bounds {α u : ℝ} (hα : 0≤α) (hα1 : α≤1) (hu : u∈Icc (0:ℝ) 1) :
    0≤ entropyCap α u ∧ entropyCap α u≤1 := by
  have h0 := entropyCap_monotone hα hα1 hu.1
  have h1 := entropyCap_monotone hα hα1 hu.2
  rw [entropyCap_linear (by norm_num),mul_zero] at h0
  rw [entropyCap_one (u := 1) (by norm_num)] at h1
  exact ⟨h0,h1⟩
lemma entropyCap_lower {α u : ℝ} (hα : 0≤α) (hα1 : α≤1) (hu : u∈Icc (0:ℝ) 1) :
    (α/10000)*u≤ entropyCap α u := by
  by_cases hh : u≤1/10000
  · rw [entropyCap_linear hh]
    nlinarith [mul_nonneg hα hu.1]
  · have hh' := entropyCap_monotone hα hα1 (le_of_not_ge hh)
    rw [entropyCap_linear (by norm_num : (1/10000:ℝ)≤1/10000)] at hh'
    nlinarith [mul_nonneg hα (sub_nonneg.mpr hu.2)]
end StandardMapEntropy

end OAI
