import OAI.MeasureTheory.Falconer.Angular.AngularPairCircleIntegral

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def angularOriginalSpatialKernel (β γ : Plane → UnitCircle → ℂ)
    (v : ℝ) (Ψ : ℝ → ℝ) (x : Fin 4 → Plane) : ℂ :=
  ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
    (angularPairCircleIntegral β (x 0) (x 1) r *
     angularPairCircleIntegral γ (x 2) (x 3) r))

theorem angularOriginalSpatialKernel_integrable
    (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) :
    Integrable (angularOriginalSpatialKernel β γ v Ψ) μ := by
  let bs : Fin 4 → Plane → UnitCircle → ℂ := ![β,β,γ,γ]
  let B : Fin 4 → ℝ := ![D₁,D₁,D₂,D₂]
  have hbs : ∀ i, Measurable (fun p : Plane × UnitCircle => bs i p.1 p.2) := by
    intro i; fin_cases i <;> assumption
  have hB : ∀ i, 0 ≤ B i := by intro i; fin_cases i <;> assumption
  have hb : ∀ i x u, ‖bs i x u‖ ≤ B i := by intro i; fin_cases i <;> assumption
  have hi := graphOriginalKernel_integrable μ bs (fun _ => 1) hbs measurable_const B hB hb
    (by intro p; simp) hΨ hs hC hc (by positivity : (0:ℝ) < (2:ℝ)^v)
  have hsli (x : Fin 4 → Plane) : Integrable
      (fun p => graphOriginalKernel bs (fun _ => 1) Ψ ((2:ℝ)^v) p x)
      (volume.prod (sourceArcLength.prod sourceArcLength)) := by
    have hh := graphOriginalKernel_integrable (Measure.dirac x) bs (fun _ => 1)
      hbs measurable_const B hB hb (by intro p; simp) hΨ hs hC hc
      (by positivity : (0:ℝ) < (2:ℝ)^v)
    simpa only [integral_dirac] using hh.integral_prod_left
  have he (x : Fin 4 → Plane) :
      (∫ p, graphOriginalKernel bs (fun _ => 1) Ψ ((2:ℝ)^v) p x
        ∂volume.prod (sourceArcLength.prod sourceArcLength)) =
      ∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
        (angularPairCircleIntegral β (x 0) (x 1) r *
         angularPairCircleIntegral γ (x 2) (x 3) r) := by
    rw [integral_prod _ (hsli x)]
    apply integral_congr_ae
    filter_upwards with r
    rw [circle_pair_integral (fun p => graphOriginalKernel bs (fun _ => 1) Ψ ((2:ℝ)^v) (r,p) x)
      ((graphOriginalKernel_measurable bs (fun _ => 1) hbs measurable_const hΨ _).comp
        (show Measurable (fun p : UnitCircle × UnitCircle => ((r,p),x)) from by fun_prop))
      (fun p => graphOriginalKernel_norm_le bs (fun _ => 1) B hB hb (by intro p; simp)
        hC hc _ (r,p) x)]
    simp only [graphOriginalKernel,integral_smul,bs,angular_four_kernel_pair_integral]
  have hh := hi.integral_prod_right.smul (((2:ℝ)^v)⁻¹)
  change Integrable (fun x => ((2:ℝ)^v)⁻¹ • (∫ p,
    graphOriginalKernel bs (fun _ => 1) Ψ ((2:ℝ)^v) p x
      ∂volume.prod (sourceArcLength.prod sourceArcLength))) μ at hh
  simp_rw [he] at hh
  exact hh

end PlanarFalconer

end OAI
