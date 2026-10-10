import OAI.Analysis.KadisonKastler.PositiveIsometryPullback

namespace OAI

/-! # Noncollinear projection witnesses in a modular corner

The corner reference is pulled back by the isometry and normalized. Its
faithfulness and polar conjugation are constructed, so the local witness
requires no independent corner standard-form or state-transitivity premise.
-/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance positiveCornerWitnessRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem positive_corner_projection_witness
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (η : H) (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hsep : Function.Injective (algebraVectorMap M η)) (hneη : η≠0)
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (q : AlgebraProjection M) (v : Algebra M) (hv : star v*v=1) (hq : v*star v=q.val)
    (ζ : H) (hζ : J ζ=ζ) (hnζ : modularQuadratic J (star v) ζ≠0)
    (hne : normalize (modularQuadratic J (star v) ζ)≠normalize (modularQuadratic J (star v) η))
    (hne' : normalize (modularQuadratic J (star v) ζ)≠-normalize (modularQuadratic J (star v) η))
    {δ : ℝ} (hδ : 0 < δ) :
    let ρ := normalize (modularQuadratic J (star v) η)
    let τ := normalize (modularQuadratic J (star v) ζ)
    let x := modularQuadratic J v ρ
    let y := modularQuadratic J v τ
    ∃ p : AlgebraProjection M, p.val≠0 ∧ p≤q ∧
      (1-(inner ℂ ρ τ).re^2)*(‖p.val.val x‖^2+‖p.val.val y‖^2) <
        16384*‖centralVectorDefect J y p.val.val‖^2 ∧
      ‖centralVectorDefect J x p.val.val‖^2 < δ*‖centralVectorDefect J y p.val.val‖^2 := by
  let ρ := normalize (modularQuadratic J (star v) η)
  let τ := normalize (modularQuadratic J (star v) ζ)
  obtain ⟨hρ,hsρ,huρ⟩ := positive_isometry_pullback_normalized
    J hJ hright ξ hξ hpos hη hsep hneη v hv
  have hcρ := cyclic_of_separating_of_conjugation_fixed J hJ hleft
    (modularPositiveCone_fixed J hright ξ hξ hρ) hsρ
  have ht : J τ=τ := by
    change J (‖modularQuadratic J (star v) ζ‖⁻¹ • modularQuadratic J (star v) ζ)=_
    rw [conjugateIsometry_real_smul,modularQuadratic_fixed J hJ hright (star v) hζ]
    rfl
  obtain ⟨r,hr,hm,hd⟩ := positive_reference_noncollinear_projection_witness
    J hJ hright hleft ξ hξ hpos hρ huρ hsρ hcρ hIII hremote τ ht
    (norm_normalize hnζ) hne hne' hδ
  refine ⟨isometryProjectionImage v hv r,isometryProjectionImage_nonzero v hv r hr,
    isometryProjectionImage_le v hv q r hq,?_,?_⟩
  · change (1-(inner ℂ ρ τ).re^2)*
      (‖(v*r.val*star v).val (modularQuadratic J v ρ)‖^2+
       ‖(v*r.val*star v).val (modularQuadratic J v τ)‖^2) <
      16384*‖centralVectorDefect J (modularQuadratic J v τ) (v*r.val*star v).val‖^2
    rw [isometry_sandwich_modular_left_norm J hJ hright v r.val hv ρ,
      isometry_sandwich_modular_left_norm J hJ hright v r.val hv τ,
      isometry_sandwich_modular_defect_norm J hJ hright v r.val hv τ]
    exact hm
  · change ‖centralVectorDefect J (modularQuadratic J v ρ) (v*r.val*star v).val‖^2 <
      δ*‖centralVectorDefect J (modularQuadratic J v τ) (v*r.val*star v).val‖^2
    rw [isometry_sandwich_modular_defect_norm J hJ hright v r.val hv ρ,
      isometry_sandwich_modular_defect_norm J hJ hright v r.val hv τ]
    exact hd

end

end KadisonKastler

end OAI
