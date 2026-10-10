import OAI.MeasureTheory.Falconer.Fourier.EndpointTransform

namespace OAI

/-!
# Eligible cell--cap incidences

Positive incidence supplies one point--angle witness. Zero incidence
annihilates the endpoint transform on almost every angle in the cap,
simultaneously for every radial frequency. The symbols need only be
measurable in the spatial variable.
-/

namespace Falconer
open Set MeasureTheory

noncomputable def capIncidence {d : ℕ} (ρ : Measure (Space d))
    (η : Sphere d → ℝ) (b : Space d → Sphere d → ℂ) : ℝ :=
  ∫ w, η w * (∫ x, ‖b x w‖^2 ∂ρ) ∂sphereMeasure d

theorem capIncidence_witness {d : ℕ} (ρ : Measure (Space d))
    (η : Sphere d → ℝ) (b : Space d → Sphere d → ℂ)
    (hη : ∀ w, 0 ≤ η w) (P : Space d → Prop)
    (hP : ∀ᵐ x ∂ρ, P x) (hinc : 0 < capIncidence ρ η b) :
    ∃ x w, P x ∧ 0 < η w ∧ b x w ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_ne_zero_of_integral_ne_zero hinc.ne'
  have hηne : η w ≠ 0 := left_ne_zero_of_mul hw
  have hxne : (∫ x, ‖b x w‖^2 ∂ρ) ≠ 0 := right_ne_zero_of_mul hw
  obtain ⟨x, hx, hPx⟩ :=
    ((frequently_ae_ne_zero_of_integral_ne_zero hxne).and_eventually hP).exists
  refine ⟨x,w,hPx,lt_of_le_of_ne (hη w) (Ne.symm hηne),?_⟩
  intro hb
  exact hx (by simp [hb])

theorem endpoint_square_integrable {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (b : Space d → Sphere d → ℂ) (hb : Measurable (Function.uncurry b))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x w, ‖b x w‖ ≤ C) (w : Sphere d) :
    Integrable (fun x => ‖b x w‖^2) ρ := by
  apply Integrable.of_bound
    ((hb.comp (measurable_id.prodMk measurable_const)).norm.pow_const 2).aestronglyMeasurable (C^2)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hbound x w)

theorem endpoint_square_le {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (b : Space d → Sphere d → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x w, ‖b x w‖ ≤ C) (w : Sphere d) :
    (∫ x, ‖b x w‖^2 ∂ρ) ≤ C^2 * ρ.real univ := by
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hbound x w)

/-- A null cell--cap incidence is removed as an integrated whole. There is
no frequency-dependent exceptional set of angles. -/
theorem capIncidence_zero_transform {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (η : Sphere d → ℝ) (hηm : Measurable η) (hη : ∀ w, 0 ≤ η w)
    (b : Space d → Sphere d → ℂ) (hb : Measurable (Function.uncurry b))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hηB : ∀ w, η w ≤ B) (hbound : ∀ x w, ‖b x w‖ ≤ C)
    (hzero : capIncidence ρ η b = 0) (M : ℝ) :
    ∀ᵐ w ∂sphereMeasure d, 0 < η w → ∀ r, endpointTransform ρ M b r w = 0 := by
  have hinner (w : Sphere d) : 0 ≤ ∫ x, ‖b x w‖^2 ∂ρ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hnonneg (w : Sphere d) : 0 ≤ η w * (∫ x, ‖b x w‖^2 ∂ρ) :=
    mul_nonneg (hη w) (hinner w)
  have hm : Measurable (fun w => η w * (∫ x, ‖b x w‖^2 ∂ρ)) :=
    hηm.mul ((hb.norm.pow_const 2).stronglyMeasurable.integral_prod_left.measurable)
  have hi : Integrable (fun w => η w * (∫ x, ‖b x w‖^2 ∂ρ)) (sphereMeasure d) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (B * (C^2 * ρ.real univ))
    filter_upwards with w
    change ‖η w * (∫ x, ‖b x w‖^2 ∂ρ)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg w)]
    exact mul_le_mul (hηB w) (endpoint_square_le ρ b hC hbound w) (hinner w) hB
  have hnull := (integral_eq_zero_iff_of_nonneg hnonneg hi).mp hzero
  filter_upwards [hnull] with w hw
  intro hwpos
  have hsq : (∫ x, ‖b x w‖^2 ∂ρ) = 0 := (mul_eq_zero.mp hw).resolve_left hwpos.ne'
  have hbx := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖b x w‖)
    (endpoint_square_integrable ρ b hb hC hbound w)).mp hsq
  intro r
  unfold endpointTransform
  suffices hh : (∫ x, Complex.exp (Complex.I * (r : ℂ) *
      (inner ℝ (w : Space d) x : ℂ)) * b x w ∂ρ) = 0 by rw [hh, smul_zero]
  apply integral_eq_zero_of_ae
  filter_upwards [hbx] with x hx
  change ‖b x w‖^2 = 0 at hx
  have hz : b x w = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (b x w)])
  simp [hz]

theorem capIncidence_zero_weightedIntegral {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (η : Sphere d → ℝ) (hηm : Measurable η) (hη : ∀ w, 0 ≤ η w)
    (b : Space d → Sphere d → ℂ) (hb : Measurable (Function.uncurry b))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hηB : ∀ w, η w ≤ B) (hbound : ∀ x w, ‖b x w‖ ≤ C)
    (hzero : capIncidence ρ η b = 0) (M r : ℝ) (F : Sphere d → ℂ) :
    (∫ w, η w • (endpointTransform ρ M b r w * F w) ∂sphereMeasure d) = 0 := by
  have hz := capIncidence_zero_transform ρ η hηm hη b hb hB hC hηB hbound hzero M
  apply integral_eq_zero_of_ae
  filter_upwards [hz] with w hw
  by_cases h : η w = 0
  · simp [h]
  · rw [hw (lt_of_le_of_ne (hη w) (Ne.symm h)) r, zero_mul, smul_zero]
    rfl

end Falconer

end OAI
