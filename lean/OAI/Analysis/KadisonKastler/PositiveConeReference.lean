import OAI.Analysis.KadisonKastler.ModularPositiveReal

namespace OAI

/-! # Changing the reference inside the generated positive cone

A positive reference vector generates a subcone of the original cone.
An invertible quadratic change of reference generates exactly the same
cone; the inverse quadratic action proves the reverse inclusion.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem modularPositiveCone_mono_reference
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    {ξ η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ) :
    modularPositiveCone (M := M) J η ≤ modularPositiveCone (M := M) J ξ := by
  have hh : ConvexCone.hull ℝ
      (Set.range (fun a : Algebra M => modularQuadratic J a η)) ≤
      modularPositiveCone (M := M) J ξ := by
    apply ConvexCone.hull_min
    rintro _ ⟨a,rfl⟩
    exact modularQuadratic_preserves_positiveCone J hJ hright ξ a hη
  exact closure_minimal hh (modularPositiveCone_isClosed J ξ)

theorem modularPositiveCone_eq_of_mutual_reference
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    {ξ η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hξ : ξ ∈ modularPositiveCone (M := M) J η) :
    modularPositiveCone (M := M) J η = modularPositiveCone (M := M) J ξ :=
  le_antisymm (modularPositiveCone_mono_reference J hJ hright hη)
    (modularPositiveCone_mono_reference J hJ hright hξ)

theorem modularPositiveCone_invertible_quadratic
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a : (Algebra M)ˣ) :
    modularPositiveCone (M := M) J (modularQuadratic J (a : Algebra M) ξ) =
      modularPositiveCone (M := M) J ξ := by
  apply modularPositiveCone_eq_of_mutual_reference J hJ hright
    (modularQuadratic_mem_positiveCone J ξ (a : Algebra M))
  have h := modularQuadratic_mem_positiveCone J
    (modularQuadratic J (a : Algebra M) ξ) ((a⁻¹ : (Algebra M)ˣ) : Algebra M)
  have he : modularQuadratic J ((a⁻¹ : (Algebra M)ˣ) : Algebra M)
      (modularQuadratic J (a : Algebra M) ξ) = ξ := by
    change (modularQuadratic J ((a⁻¹ : (Algebra M)ˣ) : Algebra M) *
      modularQuadratic J (a : Algebra M)) ξ = ξ
    rw [modularQuadratic_mul J hJ hright]
    simp only [Units.inv_mul,modularQuadratic,OneMemClass.coe_one,
      conjugationOperator_one J hJ,one_mul,one_apply_eq_self]
  rwa [he] at h

end

end KadisonKastler

end OAI
