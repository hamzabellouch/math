import OAI.NumberTheory.DirichletL.Reflection.KernelIntegral

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform
noncomputable section
universe u

theorem reflected_finite_source_uniform
    (a b : ℝ) (ha : 0<a) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧
      HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ C QK QP Qn Qb r : ℝ, 0<C → 0<QK → 0<QP → 0<Qn → 0<Qb → 0<r →
      let R := kernelCenter C QK QP Qn Qb
      (∀ {κ : Type u} (source : Finset κ) (coeff : κ→ℂ) (k p n q : κ→ℝ),
        (∀ j ∈ source, 0<k j ∧ 0<p j ∧ 0<n j ∧ 0<q j) →
        (∑ j ∈ source, coeff j *
          ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (k j) (p j) (n j) (q j) i)) /
            ((r*Real.sqrt (n j)*q j:ℝ):ℂ) *
            CubicReflectionKernel.paperKernel (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ))
              (C*n j*(q j)^3/((k j)^2*(p j)^2)))) =
        ((Real.exp (M 2/2+M 3)/(r*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            ∑ j ∈ source, coeff j *
              (kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (k j)*
                kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (p j)*
                kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (n j) (q j))) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := reflected_kernel_uniform_separation
    a b ha (reciprocalKernelWindows windows M) M hM
      (reciprocalKernelWindows_support windows M hwindows) W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro θ C QK QP Qn Qb r hC hQK hQP hQn hQb hr
  obtain ⟨he,hi,hm,hp⟩ := hsep θ C QK QP Qn Qb hC hQK hQP hQn hQb
  have hR : 0<kernelCenter C QK QP Qn Qb := by unfold kernelCenter; positivity
  have hdi := reflected_density_integrable U W hUs.continuous.measurable
    a b ha hWsupport hW θ _ hR J hi
  refine ⟨?_,hdi,hi,hm,hp⟩
  intro κ source coeff k p n q hn
  apply kernel_finite_contraction source coeff _ _ hdi _
    (reciprocalKernelWindows windows M) QK QP Qn Qb k p n q
  intro j hj
  rw [reciprocal_source_window_identity windows M QK QP Qn Qb
    (k j) (p j) (n j) (q j) r hQn hQb (hn j hj).2.2.1 (hn j hj).2.2.2 hr]
  rw [mul_assoc,he (k j) (p j) (n j) (q j) (hn j hj).1 (hn j hj).2.1 (hn j hj).2.2.1 (hn j hj).2.2.2,
    Complex.ofReal_mul]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
