import OAI.Geometry.RCD.Heat.EntropyPowerBarrier

namespace OAI

/-! # Continuity of the dimensional entropy rate at zero distance as well -/

open Set Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

def sinhSlope (q : ℝ) : ℝ := Function.update (fun q : ℝ => Real.sinh q/q) 0 1 q

@[simp] theorem sinhSlope_zero : sinhSlope 0=1 := by simp [sinhSlope]

theorem sinhSlope_of_ne_zero {q : ℝ} (hq : q ≠ 0) : sinhSlope q=Real.sinh q/q := by
  simp only [sinhSlope,Function.update_of_ne hq]

theorem continuous_sinhSlope : Continuous sinhSlope := by
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hq : q=0
  · subst q
    unfold sinhSlope
    simpa only [Real.cosh_zero,Real.sinh_zero,sub_zero] using (Real.hasDerivAt_sinh 0).continuousAt_div
  · have he : sinhSlope =ᶠ[𝓝 q] fun x : ℝ => Real.sinh x/x := by
      filter_upwards [eventually_ne_nhds hq] with x hx
      exact sinhSlope_of_ne_zero hx
    exact ((Real.continuous_sinh.continuousAt).div continuousAt_id hq).congr he.symm

theorem entropyPowerRate_formula {N c A B : ℝ} (hc : 0 ≤ c) :
    entropyPowerRate N c A B = N/(sinhSlope (Real.sqrt c))*(Real.cosh (Real.sqrt c)-B/A) := by
  by_cases h : c=0
  · simp [entropyPowerRate,h]
  · have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne hc (Ne.symm h))).ne'
    simp only [entropyPowerRate,h,↓reduceIte,sinhSlope_of_ne_zero hs]
    field_simp

 theorem tendsto_entropyPowerRate {ι : Type*} {l : Filter ι} {c a b : ι → ℝ} {c₀ a₀ b₀ N : ℝ}
    (hc : ∀ i, 0 ≤ c i) (hc₀ : 0 ≤ c₀) (ha₀ : a₀ ≠ 0)
    (hcl : Tendsto c l (𝓝 c₀)) (hal : Tendsto a l (𝓝 a₀)) (hbl : Tendsto b l (𝓝 b₀)) :
    Tendsto (fun i => entropyPowerRate N (c i) (a i) (b i)) l
      (𝓝 (entropyPowerRate N c₀ a₀ b₀)) := by
  have hs : sinhSlope (Real.sqrt c₀) ≠ 0 := by
    by_cases hz : c₀=0
    · simp [hz]
    · have hp : 0 < Real.sqrt c₀ := Real.sqrt_pos.mpr (lt_of_le_of_ne hc₀ (Ne.symm hz))
      rw [sinhSlope_of_ne_zero hp.ne']
      exact div_ne_zero (Real.sinh_pos_iff.mpr hp).ne' hp.ne'
  simp_rw [entropyPowerRate_formula (hc _)]
  rw [entropyPowerRate_formula hc₀]
  exact (tendsto_const_nhds.div (continuous_sinhSlope.tendsto _ |>.comp (Real.continuous_sqrt.tendsto _ |>.comp hcl)) hs).mul
    ((Real.continuous_cosh.tendsto _ |>.comp (Real.continuous_sqrt.tendsto _ |>.comp hcl)).sub (hbl.div hal ha₀))

end RegularPointCoordinates

end

end OAI
