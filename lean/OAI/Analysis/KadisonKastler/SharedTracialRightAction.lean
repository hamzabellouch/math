import OAI.Analysis.KadisonKastler.IrreducibleTracialState
import OAI.Analysis.KadisonKastler.ConjugateRightAlgebra

namespace OAI

/-! # A shared tracial right action determines the neighboring vector state -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem StandardTracialPosition.common_right_representatives
    {M N R : VonNeumannAlgebra H} (p : StandardTracialPosition M) (hRM : R ≤ M)
    (hright : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ N.commutant)
    (r : Algebra R) :
    ∃ b : H →L[ℂ] H, b ∈ N.commutant ∧ b p.vector = r.val p.vector ∧
      star b p.vector = star r.val p.vector := by
  let b := conjugationOperator p.conjugation (star r.val)
  have hb : b ∈ N.commutant := hright
    ⟨star r.val, R.toStarSubalgebra.star_mem' r.property, rfl⟩
  refine ⟨b, hb, ?_, ?_⟩
  · change p.conjugation (star r.val (p.conjugation p.vector)) = r.val p.vector
    rw [p.conjugation_vector]
    have he := p.conjugation_algebraVector (star (coordinateInclusion hRM r))
    change p.conjugation (star r.val p.vector) = star (star r.val) p.vector at he
    simpa only [star_star] using he
  · change star (conjugationOperator p.conjugation (star r.val)) p.vector = _
    rw [← conjugationOperator_star p.conjugation p.conjugation_involutive, star_star]
    change p.conjugation (r.val (p.conjugation p.vector)) = star r.val p.vector
    rw [p.conjugation_vector]
    exact p.conjugation_algebraVector (coordinateInclusion hRM r)

/-- Once the right action is aligned, the same unit vector implements
the neighboring factor's trace. -/
theorem StandardTracialPosition.neighbor_trace
    {M N R : VonNeumannAlgebra H} (p : StandardTracialPosition M)
    (hRM : R ≤ M) (hRN : R ≤ N)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (hirr : ∀ a : Algebra N, a.val ∈ R.commutant → ∃ c : ℂ, a = c • 1)
    (hright : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ N.commutant)
    (x : Algebra N) :
    inner ℂ p.vector (x.val p.vector) = (concreteFactorTrace hN).toLinearMap x :=
  ii1_vector_state_eq_trace_of_relative_central N R hRN hN hirr
    p.vector p.vector_norm
    (vector_state_central_of_commuting_right_representatives N R hRN p.vector
      (p.common_right_representatives hRM hright)) x

end

end KadisonKastler

end OAI
