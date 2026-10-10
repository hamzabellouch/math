import OAI.Analysis.KadisonKastler.MatrixCommonPositionConstruction
import OAI.Analysis.KadisonKastler.ConstructedMatrixFactorStability
import OAI.Analysis.KadisonKastler.MatrixStagesInClosure

namespace OAI

/-! # Finite-factor stability with the common tracial position constructed -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M N : VonNeumannAlgebra H}

theorem constructed_common_matrix_subfactor_spatial_stability
    (hBoundary : PublishedBoundary.{u})
    (hTom : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] [TopologicalSpace.SeparableSpace K], PublishedFieldTomiyamaFamily K)
    (hM : IsII1Factor M.toStarSubalgebra) (hN : IsII1Factor N.toStarSubalgebra)
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (hRN : FiniteMatrixStage.generatedVonNeumann A ≤ N)
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra (FiniteMatrixStage.generatedVonNeumann A),
        coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le A) r * a =
          a * coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le A) r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    {g : ℝ} (hg : 0 < g) (hgp : g < 174 / 1000000000000000)
    (hgap : kkDistance M N < g)
    (hstandard : 3 * 50948 * Real.sqrt g < 1 / 100000)
    (hspatial : commonPositionError g < 1 / 4000000) :
    ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧
      ‖(v : H →L[ℂ] H) - 1‖ ≤ 4000000 * commonPositionError g := by
  obtain ⟨d⟩ := exists_commonTracialPosition_of_matrixStages
    (FiniteMatrixStage.generatedVonNeumann_le A) hRN hM hN (matrixStagesInClosure A)
    (by simpa only [matrixStagesInClosure_algebra] using hA)
    (matrixStagesInClosure_generated A) hirr hg hgp
    (nearInclusion_of_kkDistance_lt hgap)
    (nearInclusion_of_kkDistance_lt (by rwa [kkDistance_comm]))
  have hsqrt : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have hb : 2 * d.tolerance < 3 * 50948 * Real.sqrt g := by
    nlinarith only [d.tolerance_lt, hsqrt]
  obtain ⟨θ, hθ⟩ := d.exists_finiteFactor_isomorphism hBoundary
    (hTom (faithfulCyclicSpace M)) hM hN hirr hgap hb hstandard
  have he : 0 ≤ commonPositionError g := by unfold commonPositionError; positivity
  have hθ' (x : Algebra M) :
      ‖(x : H →L[ℂ] H) - (θ x : H →L[ℂ] H)‖ ≤ commonPositionError g * ‖x‖ := by
    rw [norm_sub_rev]
    apply (hθ x).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    unfold commonPositionError
    nlinarith only [d.tolerance_lt]
  exact constructed_finiteFactor_spatial_of_near_starEquiv hM hN θ he hspatial hθ'

omit [Nontrivial H] in
theorem constructed_finiteFactor_spatial_of_matrixStages_and_boundary
    (hBoundary : PublishedBoundary.{u})
    (hTom : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] [TopologicalSpace.SeparableSpace K], PublishedFieldTomiyamaFamily K)
    (hM : IsII1Factor M.toStarSubalgebra) (hN : IsII1Factor N.toStarSubalgebra)
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra (FiniteMatrixStage.generatedVonNeumann A),
        coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le A) r * a =
          a * coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le A) r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    {t : ℝ} (ht : 0 < t)
    (htPosition : 302 * t < 174 / 1000000000000000) (hgap : kkDistance M N < t)
    (htStandard : 3 * 50948 * Real.sqrt (302 * t) < 1 / 100000)
    (htSpatial : commonPositionError (302 * t) < 1 / 4000000) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ constructedFiniteFactorError t := by
  have : Nontrivial H := by
    rcases subsingleton_or_nontrivial H with h | h
    · exact False.elim (hM.nonzero (@Subsingleton.elim (H →L[ℂ] H) inferInstance 0 1))
    · exact h
  obtain ⟨w, hRN, hw, hnear⟩ := exists_common_matrixStage_neighbor_of_kkDistance_lt
    A hA ht.le (by linarith : t ≤ 1 / 1152) hgap
  let P := unitaryConjugateAlgebra (star w) N
  have hP : IsII1Factor P.toStarSubalgebra := unitaryConjugateAlgebra_isII1 (star w) hN
  have hgapP : kkDistance M P < 302 * t := by
    change kkDistance M (unitaryConjugateAlgebra (star w) N) < _
    linarith
  obtain ⟨v, hv, hn⟩ := constructed_common_matrix_subfactor_spatial_stability
    hBoundary hTom hM hP A hA hRN hirr (by positivity) htPosition hgapP htStandard htSpatial
  exact ⟨w * v, conjugates_of_conjugated_neighbor w v hv,
    (conjugated_neighbor_displacement_le w v).trans (add_le_add hw hn)⟩

end

end KadisonKastler

end OAI
