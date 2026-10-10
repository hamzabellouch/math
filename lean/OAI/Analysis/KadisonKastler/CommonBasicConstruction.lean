import OAI.Analysis.KadisonKastler.TracialBasicConstruction
import OAI.Analysis.KadisonKastler.SharedConjugationBound

namespace OAI

/-! # Equality of the basic constructions from a shared right action -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N R : VonNeumannAlgebra H}

theorem StandardTracialPosition.common_basicConstruction
    (p : StandardTracialPosition M) (q : StandardTracialPosition N)
    (hsame : p.vector = q.vector) (hRM : R ≤ M) (hRN : R ≤ N)
    (hright : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ N.commutant) :
    Set.centralizer (Set.centralizer ((M : Set (H →L[ℂ] H)) ∪
      {(Generator.vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection})) =
    Set.centralizer (Set.centralizer ((N : Set (H →L[ℂ] H)) ∪
      {(Generator.vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection})) := by
  have hrightEq : conjugateRightAlgebra p.conjugation p.conjugation_involutive R =
      conjugateRightAlgebra q.conjugation q.conjugation_involutive R := by
    ext T
    constructor
    · rintro ⟨r, hr, he⟩
      exact ⟨r, hr, (p.right_action_eq q hsame hRM hRN hright r hr).symm.trans he⟩
    · rintro ⟨r, hr, he⟩
      exact ⟨r, hr, (p.right_action_eq q hsame hRM hRN hright r hr).trans he⟩
  have hN : Set.centralizer ((N : Set (H →L[ℂ] H)) ∪
      {(Generator.vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection}) =
      (conjugateRightAlgebra q.conjugation q.conjugation_involutive R : Set (H →L[ℂ] H)) := by
    rw [hsame]
    exact q.basicConstruction_commutant hRN
  rw [p.basicConstruction_commutant hRM, hN, hrightEq]

end

end KadisonKastler

end OAI
