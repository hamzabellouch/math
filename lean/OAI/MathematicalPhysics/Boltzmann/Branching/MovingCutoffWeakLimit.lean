import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

/-! # Weak convergence survives the diverging physical cutoff -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.moving_cutoff {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) (hf : ∀ n, Integrable (f n) μ)
    (hfn : ∀ n x, 0 ≤ f n x) {r : X → ℝ} (hr : Measurable r)
    {b : ℕ → ℝ} (hb : Tendsto b atTop atTop) :
    WeakL1Converges μ (fun n => {x | r x < b n}.indicator (f n)) g := by
  refine ⟨h.1,h.2.1,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  let s : ℕ → Set X := fun n => {x | b n ≤ r x}
  have hs n : MeasurableSet (s n) := measurableSet_le measurable_const hr
  have ht := h.moving_tail hf hfn hr hb
  have herror : Tendsto (fun n => ∫ x, ψ x*(s n).indicator (f n) x ∂μ) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
    · intro n
      calc
        _ ≤ ∫ x, |C| *(s n).indicator (f n) x ∂μ := by
          apply norm_integral_le_of_norm_le ((hf n).indicator (hs n) |>.const_mul |C|)
          filter_upwards [] with x
          rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
          rw [abs_of_nonneg (indicator_nonneg (fun x _ => hfn n x) x)]
          exact mul_le_mul_of_nonneg_right ((hC x).trans (le_abs_self C))
            (indicator_nonneg (fun x _ => hfn n x) x)
        _ = |C| *(∫ x, (s n).indicator (f n) x ∂μ) := integral_const_mul _ _
    · simpa using ht.const_mul |C|
  have hfull := h.2.2 ψ hψ ⟨C,hC⟩
  have he n : (∫ x, ψ x*{x | r x < b n}.indicator (f n) x ∂μ) =
      (∫ x, ψ x*f n x ∂μ)-(∫ x, ψ x*(s n).indicator (f n) x ∂μ) := by
    rw [← integral_sub ((hf n).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC))
      (((hf n).indicator (hs n)).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC))]
    congr 1
    ext x
    by_cases hx : r x < b n
    · have hy : x ∉ s n := not_le.mpr hx
      simp [hx,hy]
    · have hy : x ∈ s n := le_of_not_gt hx
      simp [hx,hy]
  simp_rw [he]
  simpa using hfull.sub herror

end BoltzmannNonuniqueness.Published

end

end OAI
