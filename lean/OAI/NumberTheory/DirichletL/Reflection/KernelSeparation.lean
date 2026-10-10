import OAI.NumberTheory.DirichletL.Reflection.KernelGeometry
import OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open MeasureTheory FourierBridge InverseKernelSourceUniform
noncomputable section

def kernelCoordinateWeight (w : ℝ→ℂ) (slope Q t q : ℝ) : ℂ :=
  w (Real.log (q/Q))*logPhase t (slope*Real.log (q/Q))

def kernelDualWeight (windows : Fin 4→ℝ→ℂ) (Qn Qb t n b : ℝ) : ℂ :=
  kernelCoordinateWeight (windows 2) 1 Qn t n * kernelCoordinateWeight (windows 3) 3 Qb t b

lemma kernelCoordinateWeight_norm (w : ℝ→ℂ) (slope Q t q : ℝ) :
    ‖kernelCoordinateWeight w slope Q t q‖ = ‖w (Real.log (q/Q))‖ := by
  simp only [kernelCoordinateWeight,norm_mul,logPhase_norm,mul_one]

lemma kernelDualWeight_norm_le_one (windows : Fin 4→ℝ→ℂ)
    (hw : ∀ i y, ‖windows i y‖≤1) (Qn Qb t n b : ℝ) :
    ‖kernelDualWeight windows Qn Qb t n b‖≤1 := by
  rw [kernelDualWeight,norm_mul,kernelCoordinateWeight_norm,kernelCoordinateWeight_norm]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hw _ _)).trans (hw _ _)

lemma kernelCoordinateWeight_continuous (w : ℝ→ℂ) (slope Q q : ℝ) :
    Continuous (fun t => kernelCoordinateWeight w slope Q t q) :=
  (logPhase_continuous_left _).const_mul _

lemma kernel_mode_separation (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb k p n b t : ℝ) :
    (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n b i) *
      logPhase t (kernelSlope i*kernelLogCoordinates QK QP Qn Qb k p n b i)) =
    kernelCoordinateWeight (windows 0) (-2) QK t k *
      kernelCoordinateWeight (windows 1) (-2) QP t p * kernelDualWeight windows Qn Qb t n b := by
  simp only [kernelCoordinateWeight,kernelDualWeight,kernelSlope,kernelLogCoordinates,
    Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,Fin.val_mk]
  norm_num
  ring

theorem reflected_kernel_uniform_separation (a b : ℝ) (ha : 0<a)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧
      HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ C QK QP Qn Qb : ℝ, 0<C → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter C QK QP Qn Qb
      (∀ k p n q : ℝ, 0<k → 0<p → 0<n → 0<q →
        (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n q i)) *
          CubicReflectionKernel.paperKernel (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ))
            (C*n*q^3/(k^2*p^2)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (kernelCoordinateWeight (windows 0) (-2) QK t k *
            kernelCoordinateWeight (windows 1) (-2) QP t p *
            kernelDualWeight windows Qn Qb t n q) * twistedDensity U W θ R t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := normTwistedSource_uniform_separation
    a b ha windows kernelSlope M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro θ C QK QP Qn Qb hC hQK hQP hQn hQb
  have hR : 0<kernelCenter C QK QP Qn Qb := by unfold kernelCenter; positivity
  obtain ⟨he,hi,hm,hp⟩ := hsep θ _ hR
  refine ⟨?_,hi,hm,hp⟩
  intro k p n q hk hp hn hq
  rw [actual_annular_kernel_identity C QK QP Qn Qb k p n q hQK hQP hQn hQb hk hp hn hq]
  rw [he]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by dsimp only; rw [kernel_mode_separation])

end
end SevenEighths.InverseReflectedPhase

end OAI
