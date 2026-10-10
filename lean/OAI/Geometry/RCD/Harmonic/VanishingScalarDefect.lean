import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! # Vanishing scalar defects from arbitrarily small additive errors -/

open Filter
open scoped Topology
namespace RegularPointCoordinates

theorem vanishing_scalar_defect (A B : ℕ → ℝ) {L M : ℝ}
    (hB : ∀ k, 0≤B k ∧ B k≤M)
    (happrox : ∀ τ : ℝ, 0<τ → ∃ F e : ℕ → ℝ,
      Tendsto F atTop (𝓝 L) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ k, A k≤F k*B k+e k+τ) :
    Tendsto (fun k => max 0 (A k-L*B k)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨F,e,hF,he,hbound⟩ := happrox (ε/2) (half_pos hε)
  have hc : Tendsto (fun k => |F k-L| * M+e k) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero,zero_mul,zero_add] using
      (((hF.sub_const L).abs.mul_const M).add he)
  filter_upwards [hc.eventually (gt_mem_nhds (half_pos hε))] with k hk
  have hp : (F k-L)*B k ≤ |F k-L| * M :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (hB k).1).trans
      (mul_le_mul_of_nonneg_left (hB k).2 (abs_nonneg _))
  have hd : A k-L*B k<ε := by nlinarith [hbound k]
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (le_max_left _ _)]
  exact max_lt hε hd

end RegularPointCoordinates

end OAI
