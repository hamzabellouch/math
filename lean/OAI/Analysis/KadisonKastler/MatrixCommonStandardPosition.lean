import OAI.Analysis.KadisonKastler.CommonBasicConstruction
import OAI.Analysis.KadisonKastler.ConjugateMatrixStages

namespace OAI

/-! # The standard tracial neighbor after the two matrix inclusions -/

namespace KadisonKastler

noncomputable section

open Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N R : VonNeumannAlgebra H}

theorem exists_matrix_common_standardPosition
    (p : StandardTracialPosition M) (hRM : R ≤ M) (hRN : R ≤ N)
    (hN : IsII1Factor N.toStarSubalgebra)
    (d : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hright : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ N.commutant)
    (hgap : kkDistance M N < 1 / 2)
    (hgap' : kkDistance M.commutant N.commutant < 1 / 2) :
    ∃ q : StandardTracialPosition N, q.vector = p.vector ∧
      Set.centralizer (Set.centralizer ((M : Set (H →L[ℂ] H)) ∪
        {(vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection})) =
      Set.centralizer (Set.centralizer ((N : Set (H →L[ℂ] H)) ∪
        {(vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection})) := by
  have hEM (n : ℕ) : (E n).algebra ≤ M.toStarSubalgebra := by
    intro x hx
    apply hRM
    rw [hR]
    exact subset_generatedVonNeumannAlgebra _ ((le_iSup (fun n => (E n).algebra) n) hx)
  have hi : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
    simpa only [← hR] using relative_irreducibility_of_near_increasing_matrices
      M N d E hmono hEM (by simpa only [← hR] using hirr) hgap
  let F := fun n => conjugateMatrixUnits p.conjugation p.conjugation_involutive (E n)
  have hS : conjugateRightAlgebra p.conjugation p.conjugation_involutive R =
      generatedVonNeumannAlgebra (⨆ n, (F n).algebra) := by
    rw [hR]
    exact conjugateRightAlgebra_generated_matrixStages _ _ d E
  have hSM : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ M.commutant := by
    rw [← p.conjugate_algebra_eq_commutant]
    exact conjugateRightAlgebra_mono _ _ hRM
  have hFM (n : ℕ) : (F n).algebra ≤ M.commutant.toStarSubalgebra := by
    intro x hx
    apply hSM
    rw [hS]
    exact subset_generatedVonNeumannAlgebra _ ((le_iSup (fun n => (F n).algebra) n) hx)
  have hiS := relative_irreducibility_commutant_of_conjugation
    p.conjugation p.conjugation_involutive R M p.conjugate_algebra_eq_commutant hirr
  have hi' : ∀ T ∈ N.commutant,
      (∀ r ∈ conjugateRightAlgebra p.conjugation p.conjugation_involutive R,
        r * T = T * r) → ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
    simpa only [← hS] using relative_irreducibility_of_near_increasing_matrices
      M.commutant N.commutant d F (conjugateMatrixUnits_mono _ _ d E hmono)
      hFM (by simpa only [← hS] using hiS) hgap'
  obtain ⟨q, hq⟩ := exists_neighbor_standardTracialPosition p hRM hRN hN hright hi hi'
  exact ⟨q, hq, p.common_basicConstruction q hq.symm hRM hRN hright⟩

end

end KadisonKastler

end OAI
