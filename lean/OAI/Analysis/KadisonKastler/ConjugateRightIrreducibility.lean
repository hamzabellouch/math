import OAI.Analysis.KadisonKastler.ConjugateRightAlgebra

namespace OAI

/-! # Relative irreducibility in the conjugate right algebra

The scalar relative commutant property transports through the actual
conjugate-linear operator map. In standard position its ambient image is
the commutant, so the source's left irreducibility supplies the right one.
The same central-vector identity supplies both orbit correspondences.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem conjugateRightAlgebra_mono
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {R M : VonNeumannAlgebra H} (hRM : R ≤ M) :
    conjugateRightAlgebra J hJ R ≤ conjugateRightAlgebra J hJ M := by
  rintro _ ⟨r, hr, rfl⟩
  exact ⟨r, hRM hr, rfl⟩

/-- Scalar relative commutants are preserved by conjugation. -/
theorem relative_irreducibility_conjugateRightAlgebra
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R M : VonNeumannAlgebra H)
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H)) :
    ∀ T ∈ conjugateRightAlgebra J hJ M,
      (∀ r ∈ conjugateRightAlgebra J hJ R, r * T = T * r) →
        ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
  rintro _ ⟨T, hTM, rfl⟩ hcomm
  have hc : ∀ r ∈ R, r * T = T * r := by
    intro r hr
    have he := congrArg (conjugationOperator J)
      (hcomm (conjugationOperator J r) ⟨r, hr, rfl⟩)
    simpa only [conjugationOperator_mul J hJ, conjugationOperator_twice J hJ] using he
  obtain ⟨z, hz⟩ := hirr T hTM hc
  refine ⟨star z, ?_⟩
  rw [hz, conjugationOperator_smul, conjugationOperator_one J hJ]

/-- The right relative commutant in a standard-position source is scalar. -/
theorem relative_irreducibility_commutant_of_conjugation
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R M : VonNeumannAlgebra H)
    (hJM : conjugateRightAlgebra J hJ M = M.commutant)
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H)) :
    ∀ T ∈ M.commutant,
      (∀ r ∈ conjugateRightAlgebra J hJ R, r * T = T * r) →
        ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
  rw [← hJM]
  exact relative_irreducibility_conjugateRightAlgebra J hJ R M hirr

/-- The central-vector identity gives both directions of the left/right
orbit correspondence, including the adjoint required in the reverse one. -/
theorem commonRightVector_orbit_correspondence
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R : VonNeumannAlgebra H) (Ω : H)
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω) :
    (∀ r ∈ R, ∃ s ∈ conjugateRightAlgebra J hJ R, r Ω = s Ω) ∧
    (∀ s ∈ conjugateRightAlgebra J hJ R, ∃ r ∈ R, s Ω = r Ω) := by
  constructor
  · intro r hr
    exact ⟨conjugationOperator J (star r),
      ⟨star r, R.toStarSubalgebra.star_mem' hr, rfl⟩, (hvector r hr).symm⟩
  · rintro _ ⟨r, hr, rfl⟩
    refine ⟨star r, R.toStarSubalgebra.star_mem' hr, ?_⟩
    simpa only [star_star] using hvector (star r) (R.toStarSubalgebra.star_mem' hr)

/-- The two relative scalar commutants and the common-vector identity
give actual cyclic and separating vectors for a neighbor. -/
theorem cyclic_separating_of_commonRight_irreducibility
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R N : VonNeumannAlgebra H) (hRN : R ≤ N)
    (hSN : conjugateRightAlgebra J hJ R ≤ N.commutant)
    (Ω : H) (hΩ : Ω ≠ 0)
    (hirrR : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hirrS : ∀ T ∈ N.commutant,
      (∀ s ∈ conjugateRightAlgebra J hJ R, s * T = T * s) →
        ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω) :
    DenseRange (fun x : Algebra N => x.val Ω) ∧
      DenseRange (fun x : Algebra N.commutant => x.val Ω) ∧
      (∀ a : Algebra N, a.val Ω = 0 → a = 0) ∧
      (∀ a : Algebra N.commutant, a.val Ω = 0 → a = 0) := by
  obtain ⟨hRS, hSR⟩ := commonRightVector_orbit_correspondence J hJ R Ω hvector
  exact preparedPair_cyclic_separating N R.toStarSubalgebra
    (conjugateRightAlgebra J hJ R).toStarSubalgebra hRN hSN Ω hΩ hirrR hirrS hRS hSR

/-- If `J M J = M′`, left relative irreducibility already supplies both
relative scalar commutants needed by the common-vector argument. -/
theorem cyclic_separating_of_relative_irreducible_conjugation
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R M : VonNeumannAlgebra H) (hRM : R ≤ M)
    (hJM : conjugateRightAlgebra J hJ M = M.commutant)
    (Ω : H) (hΩ : Ω ≠ 0)
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω) :
    DenseRange (fun x : Algebra M => x.val Ω) ∧
      DenseRange (fun x : Algebra M.commutant => x.val Ω) ∧
      (∀ a : Algebra M, a.val Ω = 0 → a = 0) ∧
      (∀ a : Algebra M.commutant, a.val Ω = 0 → a = 0) := by
  have hSM : conjugateRightAlgebra J hJ R ≤ M.commutant := by
    rw [← hJM]
    exact conjugateRightAlgebra_mono J hJ hRM
  exact cyclic_separating_of_commonRight_irreducibility J hJ R M hRM hSM Ω hΩ
    hirr (relative_irreducibility_commutant_of_conjugation J hJ R M hJM hirr) hvector

end

end KadisonKastler

end OAI
