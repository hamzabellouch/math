import OAI.Analysis.KadisonKastler.ModularFixedVectors
import OAI.Analysis.KadisonKastler.ConjugationFunctionalCalculus

namespace OAI

/-! # Polar conjugation commutes with the constructed modular group

Conjugation exchanges `R` and `1-R`. It therefore negates the real
regularized logarithm, while also conjugating the imaginary scalar in
its exponential. These two sign changes cancel.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem regularizedModularLog_polar_conjugation (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) {ε : ℝ} (hε : 0 < ε) :
    conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc)
      (regularizedModularLog M J Ω ε).val = -(regularizedModularLog M J Ω ε).val := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  have hcont := regularizedLogScalar_continuousOn (M := M) J Ω hε
  rw [regularizedModularLog_eq_cfc J Ω hε,
    conjugationOperator_cfc_real _ (tomitaPolarConjugation_involutive J Ω hsep hcyc)
      _ hR _ hcont, tomitaPolarConjugation_resolvent]
  have hc : ContinuousOn (regularizedLogScalar ε)
      ((fun s : ℝ => 1 - s) '' spectrum ℝ R) := by
    rintro _ ⟨s, hs, rfl⟩
    have hb := graphResolvent_spectrum_bounds J Ω hs
    have hm : ContinuousAt (fun r : ℝ => 1 - r + ε) (1 - s) := by fun_prop
    have hp : ContinuousAt (fun r : ℝ => r + ε) (1 - s) := by fun_prop
    exact ((Real.continuousAt_log (by linarith)).comp hm).continuousWithinAt.sub
      (((Real.continuousAt_log (by linarith)).comp hp).continuousWithinAt)
  have ha : cfc (fun s : ℝ => 1 - s) R = 1 - R := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun s : ℝ => s) R (by fun_prop) (by fun_prop),
      cfc_const_one ℝ R hR, cfc_id' ℝ R hR]
  have he := cfc_comp (regularizedLogScalar ε) (fun s : ℝ => 1 - s) R hR hc (by fun_prop)
  rw [ha] at he
  rw [← he]
  have hf : (regularizedLogScalar ε ∘ fun s : ℝ => 1 - s) =
      fun s => -regularizedLogScalar ε s := by
    funext s
    unfold regularizedLogScalar
    dsimp
    rw [show 1 - (1 - s) + ε = s + ε by ring]
    ring
  rw [hf, cfc_neg (regularizedLogScalar ε) R]

theorem regularizedModularGroup_polar_conjugation (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc)
      (regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) := by
  let : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have hC := tomitaPolarConjugation_involutive J Ω hsep hcyc
  let e := conjugationRealStarAlgEquiv C hC
  have he : Continuous e := (conjugationRealStarAlgEquiv_isometry C hC).continuous
  change e (NormedSpace.exp (Complex.I • ((t : ℂ) • (regularizedModularLog M J Ω ε).val))) = _
  rw [NormedSpace.map_exp e he]
  change NormedSpace.exp (conjugationOperator C
    (Complex.I • ((t : ℂ) • (regularizedModularLog M J Ω ε).val))) = _
  rw [conjugationOperator_smul, conjugationOperator_smul,
    regularizedModularLog_polar_conjugation J Ω hsep hcyc hε]
  simp only [Complex.star_def, Complex.conj_I, Complex.conj_ofReal, smul_neg, neg_smul,
    neg_neg]
  rfl

variable [SeparableSpace H]

theorem modularStrongGroup_polar_conjugation (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) :
    conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc)
      (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) := by
  ext x
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have hl := C.continuous.continuousAt.tendsto.comp
    (modularApproximation_tendsto J Ω hsep hcyc t (C x))
  have he (n : ℕ) : C (modularApproximation M J Ω n t (C x)) =
      modularApproximation M J Ω n t x :=
    congrArg (fun A : H →L[ℂ] H => A x)
      (regularizedModularGroup_polar_conjugation J Ω hsep hcyc
        (modularRegularizationScale_pos n) t)
  change Tendsto (fun n => C (modularApproximation M J Ω n t (C x))) atTop
    (𝓝 (C (modularStrongLimit J Ω hsep hcyc t (C x)))) at hl
  simp only [he] at hl
  exact tendsto_nhds_unique hl (modularApproximation_tendsto J Ω hsep hcyc t x)

end

end KadisonKastler

end OAI
