import Mathlib
import OAI.Probability.SKSupport.Moments.NormalFirstMoment

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto

lemma time_step_bound {F D : ℝ → ℝ → ℝ} (s h x z : ℝ) (hh : 0 ≤ h)
    (L : ℝ≥0)
    (hD : ∀ r ∈ Set.Icc s (s+h),
      HasDerivWithinAt (fun t => F t z) (D r z) (Set.Icc s (s+h)) r)
    (hL : ∀ r ∈ Set.Icc s (s+h), |D r z-D s x| ≤ (L:ℝ)*(|r-s|+|z-x|)) :
    |F (s+h) z-F s z-h*D s x| ≤ (L:ℝ)*h*(h+|z-x|) := by
  let g : ℝ → ℝ := fun t => F t z-t*D s x
  have hd (r : ℝ) (hr : r ∈ Set.Icc s (s+h)) :
      HasDerivWithinAt g (D r z-D s x) (Set.Icc s (s+h)) r := by
    have h2 : HasDerivWithinAt (fun t : ℝ => t*D s x) (D s x) (Set.Icc s (s+h)) r := by
      simpa using ((hasDerivAt_id r).mul_const (D s x)).hasDerivWithinAt
    exact (hD r hr).sub h2
  have hb (r : ℝ) (hr : r ∈ Set.Icc s (s+h)) :
      ‖D r z-D s x‖ ≤ (L:ℝ)*(h+|z-x|) := by
    rw [Real.norm_eq_abs]
    apply (hL r hr).trans
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    rw [abs_of_nonneg (sub_nonneg.mpr hr.1)]
    linarith [hr.2]
  have hm := (convex_Icc s (s+h)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => hd r hr) hb
    (show s ∈ Set.Icc s (s+h) by constructor <;> linarith)
    (show s+h ∈ Set.Icc s (s+h) by constructor <;> linarith)
  simp only [g, Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hh] at hm
  convert hm using 1
  · congr 1; ring
  · ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma expected_time_space_step (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0) {Y A : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y)
    (hYi : Integrable Y P) (hA : Measurable A) (M : ℝ≥0)
    (hAb : ∀ ω, |A ω| ≤ (M:ℝ)*(h:ℝ)) {F D : ℝ → ℝ → ℝ}
    (hf : ∀ t, ContDiff ℝ 3 (F t))
    (C₁ C₂ C₃ Ct L : ℝ≥0) (hC₁ : ∀ t x, |deriv (F t) x| ≤ C₁)
    (hC₂ : ∀ t x, |deriv (deriv (F t)) x| ≤ C₂)
    (hC₃ : ∀ t x, |iteratedDeriv 3 (F t) x| ≤ C₃)
    (hDm : Measurable (D s)) (hCt : ∀ x, |D s x| ≤ Ct)
    (hD : ∀ r ∈ Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)), ∀ z,
      HasDerivWithinAt (fun t => F t z) (D r z)
        (Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ))) r)
    (hL : ∀ r ∈ Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)), ∀ z x,
      |D r z-D s x| ≤ (L:ℝ)*(|r-(s:ℝ)|+|z-x|)) :
    |(∫ ω, F ((s:ℝ)+(h:ℝ)) (Y ω + (B (s+h) ω-B s ω) + A ω) ∂P) -
      (∫ ω, F s (Y ω) ∂P) - (∫ ω, deriv (F s) (Y ω)*A ω ∂P) -
      (h:ℝ) * ((∫ ω, D s (Y ω) ∂P) +
        (1/2:ℝ) * (∫ ω, deriv (deriv (F s)) (Y ω) ∂P))| ≤
      (C₃:ℝ)/6 * ((h:ℝ)*Real.sqrt (h:ℝ)*normalThirdMoment) +
      (C₂:ℝ)*(M:ℝ)*(h:ℝ) * (Real.sqrt (h:ℝ)*normalFirstMoment + (M:ℝ)*(h:ℝ)) +
      (L:ℝ)*(h:ℝ) * ((h:ℝ) + Real.sqrt (h:ℝ)*normalFirstMoment + (M:ℝ)*(h:ℝ)) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hYm := hY.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hd : Integrable (fun ω => B (s+h) ω - B s ω) P :=
    (hB.integrable_eval _).sub (hB.integrable_eval _)
  have hAi : Integrable A P := Integrable.of_bound hA.aestronglyMeasurable ((M:ℝ)*(h:ℝ))
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hAb ω))
  let Z (ω : Ω) := Y ω + (B (s+h) ω-B s ω) + A ω
  have hZi : Integrable Z P := (hYi.add hd).add hAi
  have hiF (t : ℝ) : Integrable (fun ω => F t (Z ω)) P :=
    integrable_comp_of_bounded_deriv ((hf t).differentiable (by norm_num)) C₁ (hC₁ t) hZi
  have hiD : Integrable (fun ω => D s (Y ω)) P := Integrable.of_bound
    (hDm.comp hYm).aestronglyMeasurable Ct
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hCt (Y ω)))
  let R (ω : Ω) := F ((s:ℝ)+(h:ℝ)) (Z ω)-F s (Z ω)-(h:ℝ)*D s (Y ω)
  have hiR : Integrable R P := ((hiF _).sub (hiF _)).sub (hiD.const_mul _)
  have hiDb : Integrable (fun ω => (h:ℝ)+|B (s+h) ω-B s ω|+(M:ℝ)*(h:ℝ)) P :=
    ((integrable_const _).add hd.abs).add (integrable_const _)
  have hRb : |∫ ω, R ω ∂P| ≤
      (L:ℝ)*(h:ℝ) * ((h:ℝ) + Real.sqrt (h:ℝ)*normalFirstMoment + (M:ℝ)*(h:ℝ)) := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (L:ℝ)*(h:ℝ) * ((h:ℝ)+|B (s+h) ω-B s ω|+(M:ℝ)*(h:ℝ)) ∂P := by
        apply integral_mono hiR.abs (hiDb.const_mul _)
        intro ω
        have he := time_step_bound (s:ℝ) (h:ℝ) (Y ω) (Z ω) h.coe_nonneg L
          (fun r hr => hD r hr (Z ω)) (fun r hr => hL r hr (Z ω) (Y ω))
        apply he.trans
        have hz : |Z ω-Y ω| ≤ |B (s+h) ω-B s ω|+(M:ℝ)*(h:ℝ) := by
          have hz : Z ω-Y ω = (B (s+h) ω-B s ω)+A ω := by dsimp only [Z]; ring
          rw [hz]
          have habs := abs_add_le (B (s+h) ω-B s ω) (A ω)
          linarith [hAb ω]
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg L.coe_nonneg h.coe_nonneg)
        linarith
      _ = _ := by
        have hiDa : Integrable (fun ω => (h:ℝ)+|B (s+h) ω-B s ω|) P :=
          (integrable_const _).add hd.abs
        rw [integral_const_mul, integral_add hiDa (integrable_const _),
          integral_add (integrable_const _) hd.abs, increment_abs_first hB s h]
        simp
  have hR : (∫ ω, R ω ∂P) = (∫ ω, F ((s:ℝ)+(h:ℝ)) (Z ω) ∂P) -
      (∫ ω, F s (Z ω) ∂P) - (h:ℝ)*(∫ ω, D s (Y ω) ∂P) := by
    have hiFd : Integrable (fun ω => F ((s:ℝ)+(h:ℝ)) (Z ω)-F s (Z ω)) P :=
      (hiF _).sub (hiF _)
    dsimp only [R]
    rw [integral_sub hiFd (hiD.const_mul _), integral_sub (hiF _) (hiF _),
      integral_const_mul]
  have hG := expected_control_step hB hm s h hY hYi hA M hAb (hf s)
    C₁ C₂ C₃ (hC₁ s) (hC₂ s) (hC₃ s)
  rw [hR] at hRb
  have htri := abs_add_le
    ((∫ ω, F s (Z ω) ∂P) - (∫ ω, F s (Y ω) ∂P) -
      (∫ ω, deriv (F s) (Y ω)*A ω ∂P) -
      (h:ℝ)/2*(∫ ω, deriv (deriv (F s)) (Y ω) ∂P))
    ((∫ ω, F ((s:ℝ)+(h:ℝ)) (Z ω) ∂P) - (∫ ω, F s (Z ω) ∂P) -
      (h:ℝ)*(∫ ω, D s (Y ω) ∂P))
  calc
    _ = |((∫ ω, F s (Z ω) ∂P) - (∫ ω, F s (Y ω) ∂P) -
      (∫ ω, deriv (F s) (Y ω)*A ω ∂P) -
      (h:ℝ)/2*(∫ ω, deriv (deriv (F s)) (Y ω) ∂P)) +
    ((∫ ω, F ((s:ℝ)+(h:ℝ)) (Z ω) ∂P) - (∫ ω, F s (Z ω) ∂P) -
      (h:ℝ)*(∫ ω, D s (Y ω) ∂P))| := by congr 1; dsimp only [Z]; ring
    _ ≤ _ := htri.trans (add_le_add hG hRb)

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
