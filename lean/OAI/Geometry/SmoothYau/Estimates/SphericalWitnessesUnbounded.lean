import Mathlib
import OAI.Geometry.SmoothYau.NodalMeasure.SphericalNodalFinite

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral MeasureTheory
open scoped Topology ContDiff Distributions ENNReal NNReal
namespace YauCounterexamples

theorem spherical_witnesses_unbounded (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (h : ∀ n : ℕ, SphericalLargeWitness g ((n:ℝ)+1) ((n:ℝ)+1)) :
    HasUnboundedNodalRatio g 3 := by
  classical
  choose k hk e u heB heD hu hu0 hue hreg hscore using h
  have hepos (n : ℕ) : 0<e n := lt_of_lt_of_le (by positivity : (0:ℝ)<(n:ℝ)+1) (heB n).le
  have hfin (n : ℕ) : nodalMeasure g 2 (u n) ≠ (∞ : ℝ≥0∞) := spherical_nodal_finite g (u n) (hu n) (hreg n)
  obtain ⟨D,hD,hbound⟩ := spherical_sign_nodal_real g
  have hbase : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have heratio (n : ℕ) : ((n:ℝ)+1)/(2*D) ≤ (nodalMeasure g 2 (u n)).toReal / Real.sqrt (e n) := by
    have hkpos : (0:ℝ)<k n := by exact_mod_cast (show 0<k n by have := hk n; omega)
    have hnp : (0:ℝ)≤(n:ℝ)+1 := by positivity
    have hscore' := hbound (u n) (hu n) (hreg n) (((n:ℝ)+1)*(k n:ℝ)) (mul_nonneg hnp hkpos.le) (hscore n)
    have hsqrtpos := Real.sqrt_pos.mpr (hepos n)
    have hsq := Real.sq_sqrt (hepos n).le
    have hsqrt : Real.sqrt (e n) ≤ 2*(k n:ℝ) := by
      have := heD n
      nlinarith
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<2*D) hsqrtpos).mpr
    have hh := mul_le_mul_of_nonneg_left hsqrt hnp
    nlinarith
  refine ⟨u,e,?_,?_,?_⟩
  · intro n
    exact ⟨hu n,hu0 n,hepos n,hue n,hfin n⟩
  · exact tendsto_atTop_mono (fun n => (heB n).le) hbase
  · exact tendsto_atTop_mono heratio (hbase.atTop_div_const (by positivity : (0:ℝ)<2*D))
end YauCounterexamples
end

end OAI
