import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelNear
import OAI.Analysis.RieszRectifiability.Kernel.NormalAnnularKernel

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem positiveNormalPotential_signed_decomposition {d : ℕ} (n : ℕ) (e x : Ambient d) :
    positiveNormalPotential n e x = inner ℝ e (kernel n x 0) + positiveNormalPotential n (-e) x := by
  simp only [positiveNormalPotential, positiveNormalHeight, inner_neg_left,
    kernel, sub_zero, inner_smul_right]
  by_cases h : 0 ≤ inner ℝ e x
  · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_left (le_of_not_ge h), max_eq_right (neg_nonneg.mpr (le_of_not_ge h))]
    ring

theorem negativeNormalPotential_quadratic_bound {d : ℕ} (p : ℕ) (e x : Ambient d)
    (hquad : 0 ≤ 2 * inner ℝ e x + ‖x‖ ^ 2) :
    positiveNormalPotential (p + 1) (-e) x ≤ (1 / 2 : ℝ) * inverseDistancePow p 0 x := by
  by_cases hx : x = 0
  · subst x
    rw [positiveNormalPotential_zero]
    exact mul_nonneg (by norm_num) (inverseDistancePow_nonneg p 0 0)
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hnum : positiveNormalHeight (-e) x ≤ ‖x‖ ^ 2 / 2 := by
      apply max_le
      · positivity
      · rw [inner_neg_left]
        linarith
    calc
      positiveNormalPotential (p + 1) (-e) x ≤ (‖x‖ ^ 2 / 2) / ‖x‖ ^ (p + 1 + 1) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = _ := by
        simp only [inverseDistancePow, dist_zero_left, pow_succ]
        field_simp

theorem negativeNormalPotential_integrable_of_quadratic_constraint {d : ℕ} (p : ℕ)
    (μ : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth (p + 1) G μ)
    (e : Ambient d) (hquad : ∀ x ∈ μ.support, 0 ≤ 2 * inner ℝ e x + ‖x‖ ^ 2)
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (positiveNormalPotential (p + 1) (-e)) (ball (0 : Ambient d) R) μ := by
  have hi := ((inverseDistancePow_near_integrable_and_bound p G μ hg 0 R hR).1.mono_set
    ball_subset_closedBall).const_mul (1 / 2 : ℝ)
  apply hi.mono' (positiveNormalPotential_measurable (p + 1) (-e)).aestronglyMeasurable
  filter_upwards [ae_restrict_of_ae μ.support_mem_ae] with x hx
  rw [Real.norm_of_nonneg (positiveNormalPotential_nonneg (p + 1) (-e) x)]
  exact negativeNormalPotential_quadratic_bound p e x (hquad x hx)

theorem positiveNormalPotential_integrable_of_quadratic_annuli {d : ℕ} (p : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (G : ℝ) (hg : GlobalUpperGrowth (p + 1) G μ)
    (e : Ambient d) (hquad : ∀ x ∈ μ.support, 0 ≤ 2 * inner ℝ e x + ‖x‖ ^ 2)
    (R B : ℝ) (hR : 0 < R)
    (hB : ∀ ε : ℝ, 0 < ε →
      ‖∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, kernel (p + 1) x 0 ∂μ‖ ≤ B) :
    IntegrableOn (positiveNormalPotential (p + 1) e) (ball (0 : Ambient d) R) μ := by
  have hneg := negativeNormalPotential_integrable_of_quadratic_constraint p μ G hg e hquad R hR
  apply (positiveNormalPotential_integrable_of_truncated_bounds (p + 1) μ e R
    (‖e‖ * B + ∫ x in ball (0 : Ambient d) R, positiveNormalPotential (p + 1) (-e) x ∂μ) ?_).1
  intro ε hε
  have hk := rieszKernel_integrableOn_centered_annulus (p + 1) μ ε R hε
  have hlinear : IntegrableOn (fun x => inner ℝ e (kernel (p + 1) x 0))
      (ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}) μ := by
    simpa only [innerSL_apply_apply] using! (innerSL ℝ e).integrable_comp hk
  have hn := hneg.mono_set (inter_subset_left :
    ball (0 : Ambient d) R ∩ {x | ε < ‖x‖} ⊆ ball (0 : Ambient d) R)
  calc
    _ = inner ℝ e (∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, kernel (p + 1) x 0 ∂μ) +
        ∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, positiveNormalPotential (p + 1) (-e) x ∂μ := by
      simp_rw [positiveNormalPotential_signed_decomposition (p + 1) e]
      rw [integral_add hlinear hn]
      exact congrArg (fun z => z + ∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖},
        positiveNormalPotential (p + 1) (-e) x ∂μ) ((innerSL ℝ e).integral_comp_comm hk)
    _ ≤ _ := add_le_add
      ((real_inner_le_norm e _).trans (mul_le_mul_of_nonneg_left (hB ε hε) (norm_nonneg e)))
      (setIntegral_mono_set hneg (Filter.Eventually.of_forall (positiveNormalPotential_nonneg (p + 1) (-e)))
        (Filter.Eventually.of_forall fun _ hx => hx.1))

end

end RieszRectifiability

end OAI
