import OAI.NumberTheory.Ostmann.Construction.LogCellErrorBound
import OAI.NumberTheory.Ostmann.Construction.LogCellPNTUniform
import OAI.NumberTheory.Ostmann.Construction.LogCellReindex
import OAI.NumberTheory.Ostmann.Construction.LogCellVariation

namespace OAI

open Filter MeasureTheory
open scoped Topology
namespace Ostmann.Construction

noncomputable def floorLogCellLogMass (c : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊Real.exp (c-1)⌋₊ ⌊Real.exp (c+1)⌋₊ with n.Prime,
    realLogCellWeight c n * Real.log n

theorem floorLogCellLogMass_tendsto :
    Tendsto floorLogCellLogMass atTop (𝓝 1) := by
  obtain ⟨C,hC,hvar⟩ := exists_logCell_variation_bound
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(C+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨X,hX⟩ := eventually_atTop.mp (eventually_theta_relative_error hδ)
  have hshift : Tendsto (fun c : ℝ => c-1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b+1)] with c hc
    linarith
  have hlow : Tendsto (fun c : ℝ => Real.exp (c-1)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hshift
  filter_upwards [hlow.eventually (eventually_ge_atTop X)] with c hc
  have ha : 0 < Real.exp (c-1) := Real.exp_pos _
  have hab : Real.exp (c-1) ≤ Real.exp (c+1) := Real.exp_le_exp.mpr (by linarith)
  have hbound := smooth_prime_sum_error_bound (Real.exp (c-1)) (Real.exp (c+1))
    ha.le hab (realLogCellWeight c) (realLogCellDerivative c)
    (fun t ht => realLogCellWeight_hasDerivAt c t (lt_of_lt_of_le ha ht.1))
    (realLogCellDerivative_continuousOn c _ _ ha)
    (realLogCellWeight_endpoints c).1 (realLogCellWeight_endpoints c).2 δ
    (fun t ht => hX t (hc.trans ht.1))
  rw [realLogCellWeight_integral] at hbound
  have htotal := hbound.trans (mul_le_mul_of_nonneg_left (hvar c) hδ.le)
  have heq : δ*(C+1)=ε := div_mul_cancel₀ _ (by linarith : C+1 ≠ 0)
  rw [Real.dist_eq]
  change |floorLogCellLogMass c-1| < ε
  change |floorLogCellLogMass c-1| ≤ δ*C at htotal
  exact lt_of_le_of_lt htotal (by nlinarith)

theorem logCellLogMass_tendsto :
    Tendsto (fun c : ℝ => logCellLogMass c ∅) atTop (𝓝 1) := by
  apply floorLogCellLogMass_tendsto.congr
  intro c
  rw [logCellLogMass_eq_abel_sum]
  apply Finset.sum_congr rfl
  intro n _
  dsimp [floorLogCellLogMass, realLogCellWeight, logCellWeight]
  ring

end Ostmann.Construction

end OAI
