import OAI.Analysis.KadisonKastler.ConjugateRightAlgebra

namespace OAI

/-! # The linear unitary comparing two conjugations

If both conjugations exchange an algebra and its commutant, their
composition is a spatial symmetry of the original algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def conjugationPairUnitary (J K : H ≃ₗᵢ⋆[ℂ] H) : unitary (H →L[ℂ] H) :=
  Unitary.linearIsometryEquiv.symm (K.trans J)

@[simp] theorem conjugationPairUnitary_apply (J K : H ≃ₗᵢ⋆[ℂ] H) (x : H) :
    (conjugationPairUnitary J K : H →L[ℂ] H) x=J (K x) := rfl

omit [CompleteSpace H] in
theorem involutive_isometry_symm_apply (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (x : H) : J.symm x=J x := by
  apply J.injective
  rw [J.apply_symm_apply,hJ]

theorem conjugationPairUnitary_conj (J K : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (hK : Function.Involutive K) (a : H →L[ℂ] H) :
    unitaryConj (conjugationPairUnitary J K) a=
      conjugationOperator J (conjugationOperator K a) := by
  ext x
  let e : H ≃ₗᵢ[ℂ] H := K.trans J
  change (((e : H →L[ℂ] H)*a*star (e : H →L[ℂ] H)) x)=_
  rw [e.star_eq_symm]
  change J (K (a (K.symm (J.symm x))))=J (K (a (K (J x))))
  rw [involutive_isometry_symm_apply J hJ,involutive_isometry_symm_apply K hK]

theorem conjugationPairUnitary_normalizes (J K : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (hK : Function.Involutive K)
    (hJleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (hJright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hKleft : ∀ a : Algebra M.commutant, conjugationOperator K a.val ∈ M)
    (hKright : ∀ a : Algebra M, conjugationOperator K a.val ∈ M.commutant) :
    Conjugates (conjugationPairUnitary J K) M M := by
  change unitaryConj (conjugationPairUnitary J K) '' (M : Set (H →L[ℂ] H))=
    (M : Set (H →L[ℂ] H))
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    rw [conjugationPairUnitary_conj J K hJ hK]
    exact hJleft ⟨_,hKright ⟨b,hb⟩⟩
  · intro ha
    refine ⟨conjugationOperator K (conjugationOperator J a),
      hKleft ⟨_,hJright ⟨a,ha⟩⟩,?_⟩
    rw [conjugationPairUnitary_conj J K hJ hK,
      conjugationOperator_twice K hK,conjugationOperator_twice J hJ]

theorem conjugationPairUnitary_fixes (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hJ : J Ω=Ω) (hK : K Ω=Ω) :
    (conjugationPairUnitary J K : H →L[ℂ] H) Ω=Ω := by
  rw [conjugationPairUnitary_apply,hK,hJ]

end

end KadisonKastler

end OAI
