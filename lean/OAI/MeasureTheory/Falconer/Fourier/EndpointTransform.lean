import OAI.MeasureTheory.Falconer.Estimates.SphericalEnergy

namespace OAI

/-!
# Original endpoint transforms in arbitrary dimension

The spatial measure argument is already restricted to its cell. A child
therefore uses the same endpoint symbol and the original restricted law.
The exact finite-measure splitting keeps the model-mass factors explicit.
-/

namespace Falconer
open MeasureTheory

noncomputable def endpointTransform {d : ℕ} (ρ : Measure (Space d))
    (M : ℝ) (b : Space d → Sphere d → ℂ) (r : ℝ) (w : Sphere d) : ℂ :=
  M⁻¹ • ∫ x, Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) x : ℂ)) * b x w ∂ρ

theorem endpoint_integrand_norm {d : ℕ} (b : Space d → Sphere d → ℂ)
    (r : ℝ) (w : Sphere d) (x : Space d) :
    ‖Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) x : ℂ)) * b x w‖ = ‖b x w‖ := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem measurable_endpointTransform {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (M : ℝ) (b : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) :
    Measurable (fun z : ℝ × Sphere d => endpointTransform ρ M b z.1 z.2) := by
  have hf : Measurable (fun z : (ℝ × Sphere d) × Space d =>
      Complex.exp (Complex.I * (z.1.1 : ℂ) * (inner ℝ (z.1.2 : Space d) z.2 : ℂ)) *
        b z.2 z.1.2) := by
    apply Measurable.mul
    · fun_prop
    · exact hb.comp (measurable_snd.prodMk measurable_fst.snd)
  have hi := (hf.stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable
  exact (measurable_const (a := (M⁻¹ : ℝ))).smul hi

theorem endpoint_integrand_integrable {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (b : Space d → Sphere d → ℂ) (hb : Measurable (Function.uncurry b))
    {C : ℝ} (hC : ∀ x w, ‖b x w‖ ≤ C) (r : ℝ) (w : Sphere d) :
    Integrable (fun x => Complex.exp (Complex.I * (r : ℂ) *
      (inner ℝ (w : Space d) x : ℂ)) * b x w) ρ := by
  apply (integrable_const C).mono
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · fun_prop
    · exact hb.comp (measurable_id.prodMk measurable_const)
  · filter_upwards with x
    exact (endpoint_integrand_norm b r w x).trans_le ((hC x w).trans (le_abs_self C))

theorem endpointTransform_norm_le {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    {M C : ℝ} (hM : 0 < M) (b : Space d → Sphere d → ℂ)
    (hC : ∀ x w, ‖b x w‖ ≤ C) (r : ℝ) (w : Sphere d) :
    ‖endpointTransform ρ M b r w‖ ≤ C * ρ.real Set.univ / M := by
  unfold endpointTransform
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
  have hb := norm_integral_le_of_norm_le_const (μ := ρ)
    (Filter.Eventually.of_forall (fun x => (endpoint_integrand_norm b r w x).trans_le (hC x w)))
  calc
    _ ≤ M⁻¹ * (C * ρ.real Set.univ) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hM.le)
    _ = _ := by ring

/-- Exact model-mass splitting of one endpoint transform. -/
theorem endpointTransform_sum {d : ℕ} {ι : Type*} (S : Finset ι)
    (ρ : ι → Measure (Space d)) [∀ i, IsFiniteMeasure (ρ i)]
    (Ma Mp : ℝ) (hMp : Mp ≠ 0) (b : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) {C : ℝ} (hC : ∀ x w, ‖b x w‖ ≤ C)
    (r : ℝ) (w : Sphere d) :
    endpointTransform (∑ i ∈ S, ρ i) Ma b r w =
      (Mp / Ma) • ∑ i ∈ S, endpointTransform (ρ i) Mp b r w := by
  simp only [endpointTransform]
  rw [integral_finsetSum_measure (fun i _ => endpoint_integrand_integrable (ρ i) b hb hC r w)]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  rw [div_mul_eq_mul_div, mul_inv_cancel₀ hMp, one_div]

end Falconer

end OAI
