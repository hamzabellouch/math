import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.PlanarPullbackMeasure
import OAI.Analysis.RieszRectifiability.Foundations.SmoothAnnularIntegrability
import OAI.Analysis.RieszRectifiability.Foundations.SeparatedSmoothAnnuli
import OAI.Analysis.RieszRectifiability.Kernel.NormalAnnularKernel

namespace OAI

/-!
# Normal potentials from smooth annular bounds

For a measure supported in a halfspace, pairing the smooth annular Riesz transform
with the normal identifies the weighted positive normal potential. Uniform bounds
on these transforms control truncated potential integrals and yield integrability
on the limiting ball, with bound `‖e‖ * B`.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem smooth_annular_normal_pairing {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (e : Ambient d) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R) :
    Integrable (fun x => smoothAnnularWeight (0 : Ambient d) r R hr hR x * positiveNormalPotential n e x) μ ∧
    (∫ x, smoothAnnularWeight (0 : Ambient d) r R hr hR x * positiveNormalPotential n e x ∂μ) =
      -inner ℝ e (smoothAnnularTransform n μ 0 r R hr hR) := by
  let g := smoothAnnularWeight (0 : Ambient d) r R hr hR
  have hk : Integrable (fun x => g x • kernel n 0 x) μ :=
    smoothAnnularTransform_integrable n hn G μ hg 0 r R hr hrR
  have hi : Integrable (fun x => inner ℝ e (g x • kernel n 0 x)) μ :=
    (innerSL ℝ e).integrable_comp hk
  have heq : (fun x => g x * positiveNormalPotential n e x) =ᵐ[μ]
      (fun x => -inner ℝ e (g x • kernel n 0 x)) := by
    filter_upwards [μ.support_mem_ae] with x hx
    rw [positiveNormalPotential_eq_kernel_component n e x (hside x hx),
      kernel_antisymm n x 0, smul_neg, inner_neg_right, neg_neg, real_inner_smul_right]
  refine ⟨hi.neg.congr heq.symm, ?_⟩
  calc
    _ = ∫ x, -inner ℝ e (g x • kernel n 0 x) ∂μ := integral_congr_ae heq
    _ = -inner ℝ e (∫ x, g x • kernel n 0 x ∂μ) := by
      rw [integral_neg]
      congr 1
      exact (innerSL ℝ e).integral_comp_comm hk
    _ = _ := rfl

theorem positiveNormalPotential_truncated_bound_of_smooth_annuli {d : ℕ}
    (n : ℕ) (hn : 1 ≤ n) (G : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (e : Ambient d) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (R B : ℝ) (hR : 0 < R)
    (hB : ∀ (r : ℝ) (hr : 0 < r), 2 * r ≤ R →
      ‖smoothAnnularTransform n μ 0 r R hr hR‖ ≤ B) :
    ∀ ε : ℝ, 0 < ε →
      (∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, positiveNormalPotential n e x ∂μ) ≤ ‖e‖ * B := by
  intro ε hε
  let r := min ε R / 4
  have hr : 0 < r := div_pos (lt_min hε hR) (by norm_num)
  have hsep : 2 * r ≤ R := by have hm := min_le_right ε R; dsimp [r]; linarith
  have heps : 2 * r ≤ ε := by have hm := min_le_left ε R; dsimp [r]; linarith
  let g := smoothAnnularWeight (0 : Ambient d) r R hr hR
  have hpair := smooth_annular_normal_pairing n hn G μ hg e hside r R hr hR (by linarith)
  have hnonneg (x : Ambient d) : 0 ≤ g x * positiveNormalPotential n e x :=
    mul_nonneg (smoothAnnularWeight_nonneg_of_separated 0 r R hr hR hsep x)
      (positiveNormalPotential_nonneg n e x)
  calc
    _ = ∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, g x * positiveNormalPotential n e x ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_ball.inter (measurableSet_lt measurable_const continuous_norm.measurable))] with x hx
      have hinner : 2 * r ≤ dist x (0 : Ambient d) := by simpa only [dist_zero_right] using! heps.trans hx.2.le
      have houter : dist x (0 : Ambient d) ≤ R := (mem_ball.mp hx.1).le
      have hg1 : g x = 1 := smoothAnnularWeight_eq_one_on_middle 0 r R hr hR x hinner houter
      rw [hg1, one_mul]
    _ ≤ ∫ x, g x * positiveNormalPotential n e x ∂μ :=
      integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hnonneg) hpair.1
    _ = -inner ℝ e (smoothAnnularTransform n μ 0 r R hr hR) := hpair.2
    _ ≤ |inner ℝ e (smoothAnnularTransform n μ 0 r R hr hR)| := neg_le_abs _
    _ ≤ ‖e‖ * ‖smoothAnnularTransform n μ 0 r R hr hR‖ := by
      simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e (smoothAnnularTransform n μ 0 r R hr hR)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB r hr hsep) (norm_nonneg e)

theorem positiveNormalPotential_integrable_of_smooth_annuli {d : ℕ}
    (n : ℕ) (hn : 1 ≤ n) (G : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (e : Ambient d) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (R B : ℝ) (hR : 0 < R)
    (hB : ∀ (r : ℝ) (hr : 0 < r), 2 * r ≤ R →
      ‖smoothAnnularTransform n μ 0 r R hr hR‖ ≤ B) :
    IntegrableOn (positiveNormalPotential n e) (ball (0 : Ambient d) R) μ ∧
      (∫ x in ball (0 : Ambient d) R, positiveNormalPotential n e x ∂μ) ≤ ‖e‖ * B := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  exact positiveNormalPotential_integrable_of_truncated_bounds n μ e R (‖e‖ * B)
    (positiveNormalPotential_truncated_bound_of_smooth_annuli n hn G μ hg e hside R B hR hB)

end

end RieszRectifiability

end OAI
