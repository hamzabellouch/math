import OAI.MeasureTheory.Falconer.Shells.LocalizedScalarShell
import OAI.MeasureTheory.Falconer.Shells.ScalarShellError

namespace OAI

/-! # Passing the stationary inverse estimate to the actual scalar transform

The angular normalization is removed exactly. A uniform pointwise error
costs only the relative shell length 2^(v-a), before its fixed negative
power is selected.
-/

namespace Falconer
open Set MeasureTheory

theorem scalar_shell_of_stationary_approximation (d : ℕ) (a v : ℝ)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hzero : ∀ x ≤ 0, Ψ x = 0)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (F G : ℝ → ℂ) (hF : Measurable F)
    (hG : Integrable (fun r => ‖G r‖^2) (PlanarFalconer.sourceAngularShellMeasure v Ψ))
    {ε H : ℝ}
    (herr : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ‖F r-(((2:ℝ)^((v-a)*((d:ℝ)-1)/2):ℝ):ℂ)*G r‖ ≤ ε)
    (hH : (2:ℝ)^((d:ℝ)*(v-a)) *
      (∫ r, ‖G r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤ H) :
    IntegrableOn (fun r => ‖F r‖^2) (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖F r‖^2) ≤
        2*H+2*(2:ℝ)^(v-a)*ε^2*
          (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  let C : ℝ := (2:ℝ)^((v-a)*((d:ℝ)-1)/2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hCc : (C:ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  let F₀ : ℝ → ℂ := fun r => F r/(C:ℂ)
  have hF₀ : Measurable F₀ := hF.div_const _
  have herr₀ : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ‖F₀ r-G r‖ ≤ ε/C := by
    filter_upwards [herr] with r hr
    have he : F₀ r-G r = (F r-(C:ℂ)*G r)/(C:ℂ) := by
      dsimp [F₀]
      field_simp [hCc]
    rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hC]
    exact div_le_div_of_nonneg_right hr hC.le
  obtain ⟨hF₀i,hF₀bound⟩ := scalar_shell_error_transfer
    (PlanarFalconer.sourceAngularShellMeasure v Ψ) F₀ G hF₀ hG
    (show 0 ≤ (2:ℝ)^((d:ℝ)*(v-a)) by positivity) herr₀ hH
  obtain ⟨hFi,hbound⟩ := localized_scalar_shell_from_angular_energy d a v Ψ
    hΨ hpos hzero hone F₀ hF₀ hF₀i hF₀bound
  have hrestore (r : ℝ) : (((2:ℝ)^((v-a)*((d:ℝ)-1)/2):ℝ):ℂ)*F₀ r = F r := by
    change (C:ℂ)*(F r/(C:ℂ)) = F r
    exact mul_div_cancel₀ (F r) hCc
  simp_rw [hrestore] at hFi hbound
  refine ⟨hFi,hbound.trans_eq ?_⟩
  have htwo : (2:ℝ)^(-a)*(2:ℝ)^v = (2:ℝ)^(v-a) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have hscale : (2:ℝ)^((d:ℝ)*(v-a)) = (2:ℝ)^(v-a)*C^2 := by
    rw [← scalar_angular_shell_normalization d a v,htwo]
  rw [hscale,div_pow]
  field_simp [hC.ne']

end Falconer

end OAI
