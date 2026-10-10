import OAI.Analysis.KadisonKastler.ModularPositiveCone

namespace OAI

/-! # The modular conjugation fixes the generated positive cone -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

private def conjugationFixedCone (J : H ≃ₗᵢ⋆[ℂ] H) : ConvexCone ℝ H where
  carrier := {η | J η = η}
  smul_mem' c _ η hη := by
    change J ((c : ℂ) • η) = (c : ℂ) • η
    rw [J.map_smulₛₗ,Complex.conj_ofReal,hη]
  add_mem' η hη ζ hζ := by
    change J (η+ζ) = η+ζ
    rw [map_add,hη,hζ]

theorem modularPositiveCone_fixed
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ = ξ) {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) : J η = η := by
  have hgen (a : Algebra M) : J (modularQuadratic J a ξ) = modularQuadratic J a ξ := by
    have he : J (modularQuadratic J a ξ) =
        conjugationOperator J a.val (a.val ξ) := by
      change J (a.val (J (a.val (J ξ)))) = J (a.val (J (a.val ξ)))
      rw [hξ]
    rw [he]
    exact congrArg (fun T : H →L[ℂ] H => T ξ)
      (VonNeumannAlgebra.mem_commutant_iff.mp (hright a) a.val a.property).symm
  have hh : ConvexCone.hull ℝ (Set.range (fun a : Algebra M => modularQuadratic J a ξ)) ≤
      conjugationFixedCone J := by
    apply ConvexCone.hull_min
    rintro _ ⟨a,rfl⟩
    exact hgen a
  exact closure_minimal (fun _ h => hh h)
    (isClosed_eq J.continuous continuous_id) hη

theorem reference_mem_modularPositiveCone
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (ξ : H) :
    ξ ∈ modularPositiveCone (M := M) J ξ := by
  have h := modularQuadratic_mem_positiveCone J ξ (1 : Algebra M)
  simpa only [modularQuadratic,OneMemClass.coe_one,conjugationOperator_one J hJ,
    one_mul,one_apply_eq_self] using h

end

end KadisonKastler

end OAI
