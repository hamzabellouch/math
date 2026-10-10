import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSymbolBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Function Topology

theorem fractionalSymbolKernel_continuousAt {d : ℕ} (m : ℕ) (ξ h : Ambient d) (hh : h ≠ 0) :
    ContinuousAt (fractionalSymbolKernel m ξ) h := by
  unfold fractionalSymbolKernel inverseDistancePow
  have hd : ContinuousAt (fun y : Ambient d => dist 0 y) h := continuousAt_const.dist continuousAt_id
  apply ((hd.pow (m + 1)).inv₀ (pow_ne_zero _ (dist_ne_zero.mpr (Ne.symm hh)))).mul
  fun_prop

theorem fractionalSymbolKernel_exists_positive {d : ℕ} (m : ℕ) (ξ : Ambient d) (hξ : ξ ≠ 0) :
    ∃ h : Ambient d, h ≠ 0 ∧ 0 < fractionalSymbolKernel m ξ h := by
  let h : Ambient d := ((2 * ‖ξ‖ ^ 2)⁻¹ : ℝ) • ξ
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  have hi : inner ℝ ξ h = 1 / 2 := by
    dsimp [h]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hh : h ≠ 0 := by
    intro hz
    rw [hz, inner_zero_right] at hi
    norm_num at hi
  have hp : 2 * Real.pi * inner ℝ ξ h = Real.pi := by rw [hi]; ring
  refine ⟨h, hh, ?_⟩
  unfold fractionalSymbolKernel
  rw [hp, Real.cos_pi]
  have hk : 0 < inverseDistancePow (m + 1) 0 h := by
    unfold inverseDistancePow
    exact inv_pos.mpr (pow_pos (dist_pos.mpr (Ne.symm hh)) _)
  exact mul_pos hk (by norm_num)

theorem fractionalSymbol_pos (p : ℕ) (ξ : Ambient (p + 1)) (hξ : ξ ≠ 0) :
    0 < fractionalSymbol p ξ := by
  obtain ⟨h, hh, hp⟩ := fractionalSymbolKernel_exists_positive (p + 1) ξ hξ
  have hn : {y : Ambient (p + 1) | 0 < fractionalSymbolKernel (p + 1) ξ y} ∈ 𝓝 h :=
    (fractionalSymbolKernel_continuousAt (p + 1) ξ h hh).eventually (lt_mem_nhds hp)
  have hs : 0 < (volume : Measure (Ambient (p + 1))) (support (fractionalSymbolKernel (p + 1) ξ)) :=
    ((volume : Measure (Ambient (p + 1))).measure_pos_of_mem_nhds hn).trans_le
      (measure_mono fun y hy => ne_of_gt hy)
  exact (integral_pos_iff_support_of_nonneg (fractionalSymbolKernel_nonneg (p + 1) ξ)
    (fractionalSymbolKernel_integrable p ξ)).mpr hs

end

end RieszRectifiability

end OAI
