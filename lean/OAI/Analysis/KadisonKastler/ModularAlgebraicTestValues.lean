import OAI.Analysis.KadisonKastler.ModularAlgebraicSeparation

namespace OAI

/-! # Both approximate eigenvector coordinates retain the strict test -/

namespace KadisonKastler

open MeasureTheory NaimarkZFC

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem exists_algebraic_modular_test_values
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
      ‖a.val Ω-ξ‖ < ε ∧ ‖((q : ℂ)⁻¹) • d.rightAction a Ω-ξ‖ < ε ∧
      c < (inner ℂ (a.val Ω) (T (a.val Ω))).re ∧
      c < (inner ℂ (((q : ℂ)⁻¹) • d.rightAction a Ω)
        (T (((q : ℂ)⁻¹) • d.rightAction a Ω))).re := by
  let c' := (c+(ψ T).re)/2
  have hc' : c < c' := by dsimp [c']; linarith
  have hcψ : c' < (ψ T).re := by dsimp [c']; linarith
  obtain ⟨η,hη,hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr hc') (3*‖T‖)
  let γ := min η (min 1 ε)
  have hγ : 0 < γ := lt_min hη (lt_min zero_lt_one hε)
  have hγ1 : γ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hγε : γ ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  have hγsmall : 3*‖T‖*γ < c'-c :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans_lt hsmall
  obtain ⟨a,q,ξ,hq,hξ,hvalue,ha,hb⟩ :=
    exists_algebraic_modular_test J hsep hcyc d hd S hcuts ψ hψ hinv T hT hcψ hγ
  exact ⟨a,q,ξ,hq,hξ,ha.trans_le hγε,hb.trans_le hγε,
    vector_quadratic_gt_of_near_unit T _ ξ hξ hγ1 ha.le hvalue hγsmall,
    vector_quadratic_gt_of_near_unit T _ ξ hξ hγ1 hb.le hvalue hγsmall⟩

end

end KadisonKastler

end OAI
