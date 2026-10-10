import OAI.MeasureTheory.Falconer.Angular.ScalarAngularShell

namespace OAI

/-! # Scalar shell comparison from the actual localized square integral

No global bound on the oscillatory expression is used. The positive cutoff
dominates the target shell, so integrability under its density gives target
shell integrability and the same exact dimensional normalization.
-/

namespace Falconer
open Set MeasureTheory

private theorem source_shell_weighted_integrable (v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x) (hzero : ∀ x ≤ 0, Ψ x = 0)
    (g : ℝ → ℝ) (hg : Integrable g (PlanarFalconer.sourceAngularShellMeasure v Ψ)) :
    Integrable (fun r => Ψ (r/(2:ℝ)^v)*g r) := by
  have hR : 0 < (2:ℝ)^v := by positivity
  have hd : Measurable (fun r : ℝ => ENNReal.ofReal (Ψ (r/(2:ℝ)^v)/(2:ℝ)^v)) := by
    fun_prop
  have hi := (integrable_withDensity_iff_integrable_smul' hd
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hg
  have he (r : ℝ) : (ENNReal.ofReal (Ψ (r/(2:ℝ)^v)/(2:ℝ)^v)).toReal =
      Ψ (r/(2:ℝ)^v)/(2:ℝ)^v := ENNReal.toReal_ofReal (div_nonneg (hpos _) hR.le)
  simp only [he,smul_eq_mul] at hi
  have hm := hi.const_mul ((2:ℝ)^v)
  have hm' : IntegrableOn (fun r => Ψ (r/(2:ℝ)^v)*g r) (Ioi (0:ℝ)) := by
    have heq : (fun r => (2:ℝ)^v*((Ψ (r/(2:ℝ)^v)/(2:ℝ)^v)*g r)) =
        fun r => Ψ (r/(2:ℝ)^v)*g r := by
      funext r
      field_simp [hR.ne']
    rw [heq] at hm
    exact hm
  apply (hm'.integrable_indicator measurableSet_Ioi).congr
  filter_upwards with r
  by_cases hr : r ∈ Ioi (0:ℝ)
  · exact indicator_of_mem hr _
  · rw [indicator_of_notMem hr]
    have hz := hzero (r/(2:ℝ)^v)
      (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hr) hR.le)
    simp only [hz,zero_mul]

theorem localized_dyadic_shell_domination (v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x) (hzero : ∀ x ≤ 0, Ψ x = 0)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    (F : ℝ → ℂ) (hF : Measurable F)
    (hi : Integrable (fun r => ‖F r‖^2) (PlanarFalconer.sourceAngularShellMeasure v Ψ)) :
    IntegrableOn (fun r => ‖F r‖^2) (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
      (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖F r‖^2) ≤
        (2:ℝ)^v*(∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  have hR : 0 < (2:ℝ)^v := by positivity
  have hwi := source_shell_weighted_integrable v Ψ hΨ hpos hzero
    (fun r => ‖F r‖^2) hi
  let T := Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))
  have hb (r : ℝ) : T.indicator (fun r => ‖F r‖^2) r ≤
      Ψ (r/(2:ℝ)^v)*‖F r‖^2 := by
    by_cases hr : r ∈ T
    · rw [indicator_of_mem hr]
      have he₁ : (2:ℝ)^(v-1) = (2:ℝ)^v/2 := by
        rw [Real.rpow_sub (by norm_num)]; norm_num
      have he₂ : (2:ℝ)^(v+1) = 2*(2:ℝ)^v := by
        rw [Real.rpow_add (by norm_num)]; norm_num; ring
      have hh : r/(2:ℝ)^v ∈ Icc (1/2:ℝ) 2 := by
        constructor
        · apply (le_div_iff₀ hR).mpr
          change (2:ℝ)^(v-1) ≤ r ∧ r ≤ (2:ℝ)^(v+1) at hr
          rw [he₁] at hr
          linarith [hr.1]
        · apply (div_le_iff₀ hR).mpr
          exact hr.2.trans_eq he₂
      exact le_mul_of_one_le_left (sq_nonneg _) (hone _ hh)
    · rw [indicator_of_notMem hr]
      exact mul_nonneg (hpos _) (sq_nonneg _)
  have hfi : Integrable (T.indicator (fun r => ‖F r‖^2)) := by
    apply hwi.mono' ((hF.norm.pow_const 2).indicator measurableSet_Icc).aestronglyMeasurable
    filter_upwards with r
    rw [Real.norm_eq_abs,abs_of_nonneg (indicator_nonneg (fun _ _ => sq_nonneg _) r)]
    exact hb r
  refine ⟨(integrable_indicator_iff measurableSet_Icc).mp hfi,?_⟩
  rw [PlanarFalconer.sourceAngularShellMeasure_integral v hΨ hpos hzero,
    smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hR.ne',one_mul,
    ← integral_indicator measurableSet_Icc]
  exact integral_mono hfi hwi hb

theorem localized_scalar_shell_from_angular_energy (d : ℕ) (a v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x) (hzero : ∀ x ≤ 0, Ψ x = 0)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    (F : ℝ → ℂ) (hF : Measurable F)
    (hi : Integrable (fun r => ‖F r‖^2) (PlanarFalconer.sourceAngularShellMeasure v Ψ))
    {H : ℝ} (hH : (2:ℝ)^((d:ℝ)*(v-a))*
      (∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤ H) :
    IntegrableOn (fun r => ‖(((2:ℝ)^((v-a)*((d:ℝ)-1)/2) : ℝ) : ℂ)*F r‖^2)
      (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)),
        ‖(((2:ℝ)^((v-a)*((d:ℝ)-1)/2) : ℝ) : ℂ)*F r‖^2) ≤ H := by
  have hdom := localized_dyadic_shell_domination v Ψ hΨ hpos hzero hone F hF hi
  have hp : 0 ≤ (2:ℝ)^((v-a)*((d:ℝ)-1)/2) := by positivity
  have he : (fun r => ‖(((2:ℝ)^((v-a)*((d:ℝ)-1)/2) : ℝ) : ℂ)*F r‖^2) =
      fun r => ((2:ℝ)^((v-a)*((d:ℝ)-1)/2))^2*‖F r‖^2 := by
    funext r
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp,mul_pow]
  rw [he]
  refine ⟨hdom.1.const_mul _,?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ (2:ℝ)^(-a)*(((2:ℝ)^((v-a)*((d:ℝ)-1)/2))^2*
        ((2:ℝ)^v*(∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdom.2 (sq_nonneg _)) (by positivity)
    _ = (2:ℝ)^((d:ℝ)*(v-a))*
        (∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
      rw [show (2:ℝ)^(-a)*(((2:ℝ)^((v-a)*((d:ℝ)-1)/2))^2*
          ((2:ℝ)^v*(∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ))) =
          ((2:ℝ)^(-a)*(2:ℝ)^v*((2:ℝ)^((v-a)*((d:ℝ)-1)/2))^2)*
            (∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) by ring,
        scalar_angular_shell_normalization]
    _ ≤ H := hH

end Falconer

end OAI
