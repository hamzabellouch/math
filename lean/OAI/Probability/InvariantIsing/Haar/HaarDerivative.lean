import Mathlib

namespace OAI

/-!
# Differentiating Haar rotation invariance

Infinitesimal Haar invariance gives the integral identity for spectral Ward
identities under explicit domination assumptions.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace InvariantIsing

abbrev Orthogonal (N : ℕ) := Matrix.orthogonalGroup (Fin N) ℝ

/-- A dominated infinitesimal left rotation has Haar mean zero. -/
lemma integral_rotation_derivative_eq_zero {N : ℕ} (μ : Measure (Orthogonal N))
    [μ.IsMulLeftInvariant] (R : ℝ → Orthogonal N) (hR : R 0 = 1)
    (f : Orthogonal N → ℝ) (hf : Measurable f) (hfi : Integrable f μ)
    (f' : ℝ → Orthogonal N → ℝ) (hf' : AEStronglyMeasurable (f' 0) μ)
    (B : Orthogonal N → ℝ) (hB : Integrable B μ)
    (hbound : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖f' t U‖ ≤ B U)
    (hderiv : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => f (R s * U)) (f' t U) t) :
    ∫ U, f' 0 U ∂μ = 0 := by
  have hs : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun U => f (R t * U)) μ := by
    apply Filter.Eventually.of_forall
    intro t
    have hmul : Measurable (fun U : Orthogonal N => R t * U) := by
      apply Measurable.subtype_mk
      change Measurable (fun U : Orthogonal N =>
        (R t : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ))
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro j
      simp only [Matrix.mul_apply]
      exact Finset.measurable_sum _ fun k _ =>
        measurable_const.mul ((measurable_pi_apply j).comp
          ((measurable_pi_apply k).comp measurable_subtype_coe))
    exact (hf.comp hmul).aestronglyMeasurable
  have hi : Integrable (fun U => f (R 0 * U)) μ := by simpa only [hR, one_mul] using hfi
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hi hf'
    hbound hB hderiv
  have he : (fun t => ∫ U, f (R t * U) ∂μ) = fun _ : ℝ => ∫ U, f U ∂μ := by
    funext t
    exact integral_mul_left_eq_self f (R t)
  rw [he] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) (∫ U, f U ∂μ))

end InvariantIsing

end

end OAI
