import OAI.Analysis.KadisonSimilarity.Representation.FiniteOrbitSubspace
import OAI.Analysis.KadisonSimilarity.Similarity.KirchbergUniformBound

namespace OAI

/-! Haagerup's finite cyclic reduction completes Kirchberg's Proposition 1.
Each finite matrix test vector generates an invariant subspace on which the
representation is similar. The uniform bound on these restrictions therefore
bounds every amplification of the original bounded homomorphism. -/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem completeBound_of_uniformCommutator {C : ℝ} (hC : 0 ≤ C)
    (estimate : UniformCommutatorEstimate.{v} C) (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 < M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖) :
    CompleteBound π.1 (Real.exp (C * (M + 1))) := by
  intro n X
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  by_cases hn : 0 < n
  · let E := finiteOrbitSubspace π (fun i => ξ i)
    let ρ := restrictBoundedHom π E (finiteOrbitSubspace_invariant π (fun i => ξ i))
    obtain ⟨S, hS⟩ := finiteOrbitSubspace_similar π hn (fun i => ξ i)
    have hcb : IsCompletelyBounded ρ.1 :=
      ⟨_, mul_nonneg (norm_nonneg _) (norm_nonneg _), completeBound_of_similarity ρ S hS⟩
    have hb := kirchberg_uniform_completeBound hC estimate ρ hM
      (restrictBoundedHom_bound π E (finiteOrbitSubspace_invariant π (fun i => ξ i))
        (le_of_lt hM) hπ) hcb n X
    let η : HilbertCopies E n := WithLp.toLp 2 (finiteOrbitGenerators π (fun i => ξ i))
    have hη : ‖η‖ = ‖ξ‖ := by
      have he : ‖η‖ ^ 2 = ‖ξ‖ ^ 2 := by
        simp only [PiLp.norm_sq_eq_of_L2, η, finiteOrbitGenerators]
        rfl
      nlinarith [norm_nonneg η, norm_nonneg ξ]
    have he (i : Fin n) :
        ((matrixOperator (X.map ρ.1) η i : E) : H) =
          matrixOperator (X.map π.1) ξ i := by
      simp [matrixOperator_apply, ρ, η, finiteOrbitGenerators, restrictBoundedHom_apply]
    have hnorm : ‖matrixOperator (X.map ρ.1) η‖ = ‖matrixOperator (X.map π.1) ξ‖ := by
      have hs : ‖matrixOperator (X.map ρ.1) η‖ ^ 2 =
          ‖matrixOperator (X.map π.1) ξ‖ ^ 2 := by
        simp only [PiLp.norm_sq_eq_of_L2]
        apply Finset.sum_congr rfl
        intro i _
        rw [← he i]
        rfl
      nlinarith [norm_nonneg (matrixOperator (X.map ρ.1) η),
        norm_nonneg (matrixOperator (X.map π.1) ξ)]
    calc
      ‖matrixOperator (X.map π.1) ξ‖ = ‖matrixOperator (X.map ρ.1) η‖ := hnorm.symm
      _ ≤ ‖matrixOperator (X.map ρ.1)‖ * ‖η‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (Real.exp (C * (M + 1)) * ‖CStarMatrix.ofMatrix X‖) * ‖ξ‖ := by
        rw [hη]
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · have hn0 : n = 0 := by omega
    subst n
    have hξ : ξ = 0 := Subsingleton.elim _ _
    simp [hξ]

/-- Uniform commutator control implies similarity for every bounded unital
homomorphism, including those not initially known to be completely bounded. -/
theorem similarity_of_uniformCommutator {C : ℝ} (hC : 0 ≤ C)
    (estimate : UniformCommutatorEstimate.{v} C) (π : BoundedUnitalHom A H) :
    SimilarToStar A H π := by
  let f : A →L[ℂ] (H →L[ℂ] H) := ⟨π.1.toLinearMap, π.2⟩
  have hb : ∀ a, ‖π.1 a‖ ≤ (‖f‖ + 1) * ‖a‖ := by
    intro a
    exact (f.le_opNorm a).trans (by nlinarith [norm_nonneg a])
  obtain ⟨S, _, hS⟩ := paulsenSimilarityInput π (Real.exp (C * ((‖f‖ + 1) + 1)))
    (le_of_lt (Real.exp_pos _))
    (completeBound_of_uniformCommutator hC estimate π (by positivity) hb)
  exact ⟨S, hS⟩

end KadisonSimilarity

end

end OAI
