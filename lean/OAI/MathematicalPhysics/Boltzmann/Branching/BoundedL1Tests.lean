import OAI.MathematicalPhysics.Boltzmann.Compactness.L1TruncationCauchy

namespace OAI

/-! # Continuity and norm bounds for bounded measurable L¹ tests -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem abs_integral_bounded_mul (v : X → ℝ) (hv : Integrable v μ)
    (ψ : X → ℝ) (hψ : Measurable ψ) (C : ℝ≥0) (hC : ∀ x, ‖ψ x‖ ≤ C) :
    |∫ x, ψ x*v x ∂μ| ≤ C * ∫ x, |v x| ∂μ := by
  have hi := hv.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  calc
    |∫ x, ψ x*v x ∂μ| ≤ ∫ x, |ψ x*v x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => ψ x*v x)
    _ ≤ ∫ x, (C : ℝ)*|v x| ∂μ := by
      apply integral_mono hi.abs (hv.abs.const_mul C)
      intro x
      change |ψ x*v x| ≤ (C : ℝ)*|v x|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)
    _ = C * ∫ x, |v x| ∂μ := integral_const_mul _ _

theorem abs_bounded_test_difference (v w : X → ℝ) (hv : Integrable v μ)
    (hw : Integrable w μ) (ψ : X → ℝ) (hψ : Measurable ψ) (C : ℝ≥0)
    (hC : ∀ x, ‖ψ x‖ ≤ C) :
    |(∫ x, ψ x*v x ∂μ)-(∫ x, ψ x*w x ∂μ)| ≤ C * ∫ x, |v x-w x| ∂μ := by
  have hiv := hv.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have hiw := hw.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have he : (∫ x, ψ x*v x ∂μ)-(∫ x, ψ x*w x ∂μ) =
      ∫ x, ψ x*(v x-w x) ∂μ := by
    rw [← integral_sub hiv hiw]
    congr 1
    funext x
    ring
  rw [he]
  exact abs_integral_bounded_mul (v-w) (hv.sub hw) ψ hψ C hC

theorem bounded_test_L1_tendsto {u : ℕ → Lp ℝ 1 μ} {g : Lp ℝ 1 μ}
    (hu : Tendsto u atTop (𝓝 g)) (ψ : X → ℝ) (hψ : Measurable ψ)
    (C : ℝ≥0) (hC : ∀ x, ‖ψ x‖ ≤ C) :
    Tendsto (fun n => ∫ x, ψ x*u n x ∂μ) atTop (𝓝 (∫ x, ψ x*g x ∂μ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hn : Tendsto (fun n => ‖u n-g‖) atTop (𝓝 0) := by
    simpa using (hu.sub_const g).norm
  have hlim : Tendsto (fun n => (C : ℝ)*‖u n-g‖) atTop (𝓝 0) := by
    simpa using hn.const_mul (C : ℝ)
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hlim
  rw [Real.dist_eq]
  have he : (∫ x, |u n x-g x| ∂μ) = ‖u n-g‖ := by
    rw [L1.norm_sub_eq_lintegral]
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using integral_norm_eq_lintegral_enorm
      ((L1.integrable_coeFn (u n)).sub (L1.integrable_coeFn g)).aestronglyMeasurable
  simpa only [he] using abs_bounded_test_difference (u n) g
    (L1.integrable_coeFn _) (L1.integrable_coeFn _) ψ hψ C hC

theorem scalar_tendsto_of_uniform_approximations
    (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (z : ℝ) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (herr : ∀ m n, |a n-b m n| ≤ δ m)
    (hb : ∀ m, Tendsto (b m) atTop (𝓝 (c m)))
    (hc : Tendsto c atTop (𝓝 z)) : Tendsto a atTop (𝓝 z) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hd := hδ.eventually (gt_mem_nhds (show 0 < ε/3 by positivity))
  have hz := (Metric.tendsto_atTop.mp hc (ε/3) (by positivity))
  obtain ⟨M,hM⟩ := hz
  obtain ⟨m,hm,hmδ⟩ := ((eventually_ge_atTop M).and hd).exists
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hb m) (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hb' := hN n hn
  have hc' := hM m hm
  rw [Real.dist_eq] at hb' hc' ⊢
  have htriangle := (abs_sub_le (a n) (b m n) z).trans
    (add_le_add_right (abs_sub_le (b m n) (c m) z) _)
  linarith [herr m n]

end BoltzmannNonuniqueness.Published

end

end OAI
