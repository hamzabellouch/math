import OAI.Analysis.KadisonKastler.ConjugateRightAlgebra

namespace OAI

/-! # The modular conjugation data used in preparing a pair

For a cyclic separating vector, Tomita--Takesaki gives `J M J = M′`.
The vector identity `J(r* Ω) = r Ω` is needed only for elements in the
vector-state centralizer. It is not imposed on the whole algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure ModularConjugationData (M : VonNeumannAlgebra H) (Ω : H) where
  conjugation : H ≃ₗᵢ⋆[ℂ] H
  involutive : Function.Involutive conjugation
  fixes_vector : conjugation Ω = Ω
  commutant : conjugateRightAlgebra conjugation involutive M = M.commutant
  centralizer_vector : ∀ r : Algebra M,
    (∀ x : Algebra M, inner ℂ Ω ((r.val * x.val) Ω) = inner ℂ Ω ((x.val * r.val) Ω)) →
      conjugationOperator conjugation (star r.val) Ω = r.val Ω

namespace ModularConjugationData

variable {M R : VonNeumannAlgebra H} {Ω : H} (d : ModularConjugationData M Ω)

/-- The full commutant theorem supplies the right inclusion for every
subalgebra, without requiring a trace on the source algebra. -/
theorem right_mem (hRM : R ≤ M) (r : Algebra R) :
    conjugationOperator d.conjugation r.val ∈ M.commutant := by
  change conjugationOperator d.conjugation r.val ∈ (M.commutant : Set (H →L[ℂ] H))
  rw [← d.commutant, conjugateRightAlgebra_coe]
  exact ⟨r.val, hRM r.property, rfl⟩

/-- Only centralization of the vector state on the common subalgebra is
needed for the right-vector identity in graph comparison. -/
theorem common_vector (hRM : R ≤ M)
    (hcentral : ∀ r : Algebra R, ∀ x : Algebra M,
      inner ℂ Ω ((r.val * x.val) Ω) = inner ℂ Ω ((x.val * r.val) Ω))
    (r : Algebra R) :
    conjugationOperator d.conjugation (star r.val) Ω = r.val Ω :=
  d.centralizer_vector ⟨r.val, hRM r.property⟩ (hcentral r)

end ModularConjugationData

end

end KadisonKastler

end OAI
