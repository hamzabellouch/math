import OAI.Analysis.KadisonSimilarity.Derivation.FactorizationGeometry
import OAI.Analysis.BoundedHochschild.CompletelyBoundedFactorization

namespace OAI

/-! # Quantitative similarity from the proved completely bounded factorization

The entrywise C-star matrix norm agrees with the concrete matrix operator
norm. Applying the proved factorization and then removing its kernel gives
Paulsen's quantitative similarity conclusion on the original Hilbert space.
-/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem completeBound_entrywise (π : BoundedUnitalHom A H) {C : ℝ}
    (hπ : CompleteBound π.1 C) (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖X.map π.1.toLinearMap‖ ≤ C * ‖X‖ := by
  have h := hπ n (CStarMatrix.ofMatrix.symm X)
  change ‖matrixOperator (CStarMatrix.ofMatrix.symm (X.map π.1.toLinearMap))‖ ≤ C * ‖X‖ at h
  rwa [norm_matrixOperator_eq] at h

/-- Paulsen's quantitative similarity bound, including the zero Hilbert space. -/
theorem paulsenSimilarityInput (π : BoundedUnitalHom A H) : PaulsenSimilarityInput π := by
  intro C hC hπ
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    refine ⟨1, ?_, fun _ => Subsingleton.elim _ _⟩
    have hnorm : ‖(1 : H →L[ℂ] H)‖ = 0 := by
      rw [Subsingleton.elim (1 : H →L[ℂ] H) 0, norm_zero]
    simpa only [inv_one, Units.val_one, hnorm, zero_mul] using hC
  · let := hH
    have h01 : (0 : A) ≠ 1 := by
      intro h
      have he := congrArg π.1 h
      have hz : (0 : H →L[ℂ] H) = 1 := by
        simpa only [map_zero, map_one] using he
      exact zero_ne_one hz
    let : Nontrivial A := ⟨⟨0, 1, h01⟩⟩
    have hm : (1 : CStarMatrix (Fin 1) (Fin 1) A).map π.1.toLinearMap = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      simp
    have hc := completeBound_entrywise π hπ 1 1
    rw [hm, CStarRing.norm_one, CStarRing.norm_one, mul_one] at hc
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hc
    obtain ⟨F⟩ := BoundedHochschild.KadisonRingrose.factorization_of_complete_bound
      π.1.toLinearMap hCpos (completeBound_entrywise π hπ)
    obtain ⟨S, hS, hs⟩ := quantitative_similarity_of_factorization
      π F.representation F.rightMap F.leftMap.adjoint (fun a => (F.factorization a).symm)
    refine ⟨S, hS.trans ?_, hs⟩
    simpa only [ContinuousLinearMap.adjoint.norm_map, mul_comm] using F.bound

end KadisonSimilarity

end

end OAI
