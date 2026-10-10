import OAI.Analysis.KadisonKastler.ModularLocalizedAlgebra
import OAI.Analysis.KadisonKastler.ModularUnitPacketSelection
import OAI.Analysis.KadisonKastler.VectorQuadraticContinuity

namespace OAI

/-! # Strict state tests detected by approximate modular eigenvectors

This is the separation consequence needed from the approximate-eigenstate
argument. All spectral, packet and algebraic approximations are constructed.
-/

namespace KadisonKastler

open MeasureTheory NaimarkZFC

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem exists_algebraic_modular_test
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (d : ModularConjugationData M Ω)
    (hd : d.conjugation=tomitaPolarConjugation J Ω hsep hcyc)
    (S : ModularSpectralResolution M Ω)
    (hcuts : ∀ r, S.upperCut r=modularUpperCut M J Ω r)
    (ψ : (H →L[ℂ] H) →L[ℂ] ℂ) (hψ : IsState ψ)
    (hinv : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : H →L[ℂ] H),
      ψ (stateActionAverage S.group S.continuous μ T)=ψ T)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ} (hc : c < (ψ T).re)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : Algebra M) (q : ℝ) (ξ : H), 0 < q ∧ ‖ξ‖=1 ∧
      c < (inner ℂ ξ (T ξ)).re ∧ ‖a.val Ω-ξ‖ < ε ∧
      ‖((q : ℂ)⁻¹) • d.rightAction a Ω-ξ‖ < ε := by
  let δ := Real.log (1+ε/2)
  have hδ : 0 < δ := Real.log_pos (by linarith)
  have hexp : Real.exp δ-1=ε/2 := by
    rw [Real.exp_log (by positivity)]
    ring
  obtain ⟨r,ξ,hξ,hlo,hhi,hgt⟩ := S.exists_short_spectral_unit_vector_gt ψ hψ hinv T hT hc hδ
  rw [hcuts] at hlo hhi
  obtain ⟨a,q,hq,ha,hb⟩ := modular_localized_algebra_approximate J hsep hcyc d hd ξ
    hδ.le hlo hhi (show 0 < ε/4 by positivity)
  rw [hexp,hξ,mul_one] at ha hb
  exact ⟨a,q,ξ,hq,hξ,hgt,ha.trans_le (by linarith),hb.trans_le (by linarith)⟩

end

end KadisonKastler

end OAI
