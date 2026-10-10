import OAI.MeasureTheory.Falconer.Angular.AngularTransform
import OAI.MeasureTheory.Falconer.Measures.DyadicIntegralSplitting

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem angular_integrand_norm (r : ℝ) (ω : UnitCircle) (x : Plane)
    (b : Plane → UnitCircle → ℂ) :
    ‖Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (ω : Plane) x : ℂ)) * b x ω‖ =
      ‖b x ω‖ := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem integrableOn_angular_integrand (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2))
    (C : ℝ) (hC : ∀ x ω, ‖b x ω‖ ≤ C) (r : ℝ) (ω : UnitCircle) :
    IntegrableOn (fun x =>
      Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (ω : Plane) x : ℂ)) * b x ω) X ρ := by
  apply (integrable_const C).mono
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · fun_prop
    · exact hb.comp (measurable_id.prodMk measurable_const)
  · filter_upwards with x
    rw [angular_integrand_norm]
    exact (hC x ω).trans (le_abs_self C)

theorem sourceAngularTransform_split (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (n : ℕ) (Ma Mp : ℝ) (hMp : Mp ≠ 0)
    (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2))
    (C : ℝ) (hC : ∀ x ω, ‖b x ω‖ ≤ C) (r : ℝ) (ω : UnitCircle) :
    sourceAngularTransform ρ Q.carrier Ma b r ω =
      (Mp / Ma) • ∑ P ∈ occupiedAnchorPaths Q ρ n,
        sourceAngularTransform ρ (Q.descendant P).carrier Mp b r ω := by
  unfold sourceAngularTransform
  rw [Q.integral_split_occupied hQ ρ n _ (integrableOn_angular_integrand ρ _ b hb C hC r ω)]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  rw [div_mul_eq_mul_div, mul_inv_cancel₀ hMp, one_div]

theorem sourceAngularTransform_norm_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) (M : ℝ) (hM : 0 < M) (b : Plane → UnitCircle → ℂ)
    (C : ℝ) (hC : ∀ x ∈ X, ∀ ω, ‖b x ω‖ ≤ C) (r : ℝ) (ω : UnitCircle) :
    ‖sourceAngularTransform ρ X M b r ω‖ ≤ C * (ρ X).toReal / M := by
  unfold sourceAngularTransform
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
  have hb := norm_setIntegral_le_of_norm_le_const (measure_lt_top ρ X)
    (fun x hx => (angular_integrand_norm r ω x b).trans_le (hC x hx ω))
  calc
    _ ≤ M⁻¹ * (C * (ρ X).toReal) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hM.le)
    _ = _ := by ring

theorem sourceAngularTransform_sum_norm_le (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (n : ℕ) (M : ℝ) (hM : 0 < M)
    (b : Plane → UnitCircle → ℂ) (C : ℝ) (hC : ∀ x ω, ‖b x ω‖ ≤ C)
    (r : ℝ) (ω : UnitCircle) :
    (∑ P ∈ occupiedAnchorPaths Q ρ n,
      ‖sourceAngularTransform ρ (Q.descendant P).carrier M b r ω‖) ≤
        C * (ρ Q.carrier).toReal / M := by
  calc
    _ ≤ ∑ P ∈ occupiedAnchorPaths Q ρ n, C * ((ρ (Q.descendant P).carrier).toReal / M) := by
      apply Finset.sum_le_sum
      intro P _
      simpa only [mul_div_assoc] using
        sourceAngularTransform_norm_le ρ _ M hM b C (fun x _ ω => hC x ω) r ω
    _ = _ := by rw [← Finset.mul_sum, Q.normalized_mass_split hQ ρ n M, mul_div_assoc]

end PlanarFalconer

end OAI
