import OAI.Geometry.EinsteinFour.ScalarCompactExtremal

namespace OAI

/-! Strong convergence of a minimizing sequence once its actual Lp values
converge.  This is the Hilbert-space closure step for taking absolute values. -/

namespace PositiveEinsteinFour.Geometry

open Filter
open scoped Topology

noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalar_energy_minimizing_sequence_cauchy (T : H →L[ℝ] E) (m : ℝ)
    (hmin : ∀ v : H, m * ‖T v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (u : ℕ → H) (y : E) (hy : ‖y‖ = 1)
    (hlim : Tendsto (fun n => T (u n)) atTop (𝓝 y))
    (henergy : Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 m)) : CauchySeq u := by
  have hf : Tendsto (fun nm : ℕ × ℕ => T (u nm.1)) atTop (𝓝 y) := by
    rw [← prod_atTop_atTop_eq]
    exact hlim.comp tendsto_fst
  have hs : Tendsto (fun nm : ℕ × ℕ => T (u nm.2)) atTop (𝓝 y) := by
    rw [← prod_atTop_atTop_eq]
    exact hlim.comp tendsto_snd
  have hef : Tendsto (fun nm : ℕ × ℕ => ‖u nm.1‖ ^ 2) atTop (𝓝 m) := by
    rw [← prod_atTop_atTop_eq]
    exact henergy.comp tendsto_fst
  have hes : Tendsto (fun nm : ℕ × ℕ => ‖u nm.2‖ ^ 2) atTop (𝓝 m) := by
    rw [← prod_atTop_atTop_eq]
    exact henergy.comp tendsto_snd
  have hsum : Tendsto (fun nm : ℕ × ℕ => ‖T (u nm.1 + u nm.2)‖) atTop (𝓝 2) := by
    have hy2 : ‖y + y‖ = 2 := by
      rw [← two_smul ℝ y, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hy, mul_one]
    simpa only [map_add, hy2] using (hf.add hs).norm
  have hb : Tendsto (fun nm : ℕ × ℕ =>
      2 * ‖u nm.1‖ ^ 2 + 2 * ‖u nm.2‖ ^ 2 - m * ‖T (u nm.1 + u nm.2)‖ ^ 2)
      atTop (𝓝 0) := by
    convert (hef.const_mul 2 |>.add (hes.const_mul 2)).sub ((hsum.pow 2).const_mul m) using 1
    ring_nf
  have hz : Tendsto (fun nm : ℕ × ℕ => ‖u nm.1 - u nm.2‖ ^ 2) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun _ => sq_nonneg _)
    intro nm
    have hp := parallelogram_law_with_norm ℝ (u nm.1) (u nm.2)
    have hm := hmin (u nm.1 + u nm.2)
    nlinarith
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hz
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero, dist_eq_norm] using hnorm

theorem scalar_energy_minimizing_sequence_limit [CompleteSpace H] (T : H →L[ℝ] E) (m : ℝ)
    (hmin : ∀ v : H, m * ‖T v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (u : ℕ → H) (y : E) (hy : ‖y‖ = 1)
    (hlim : Tendsto (fun n => T (u n)) atTop (𝓝 y))
    (henergy : Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 m)) :
    ∃ w : H, T w = y ∧ ‖w‖ ^ 2 = m ∧ Tendsto u atTop (𝓝 w) := by
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete
    (scalar_energy_minimizing_sequence_cauchy T m hmin u y hy hlim henergy)
  exact ⟨w, tendsto_nhds_unique (T.continuous.tendsto w |>.comp hw) hlim,
    tendsto_nhds_unique (hw.norm.pow 2) henergy, hw⟩

end
end PositiveEinsteinFour.Geometry

end OAI
