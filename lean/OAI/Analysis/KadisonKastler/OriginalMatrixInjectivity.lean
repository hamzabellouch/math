import OAI.Analysis.KadisonKastler.TraceHilbertExtension
import OAI.Analysis.KadisonKastler.MatrixRetractionTransport
import OAI.Analysis.KadisonKastler.FiniteVectorMatrixDensity
import OAI.Analysis.KadisonKastler.FiniteTraceWeakLimit

namespace OAI

/-! # Injectivity of matrix closures in the original finite-factor representation

The scalar trace is extended to the ambient operators and its GNS space
supplies a contractive extension of the trace representation. Finite matrix
retractions are transported through this extension. The finite-vector trace
formula proves convergence on the original representation.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- A trace-representation extension suffices for the original matrix closure. -/
theorem isInjective_matrix_closure_of_trace_extension
    (σ : FaithfulTracialState (Algebra M)) (hσ : FiniteVectorTrace σ)
    (τ : TracialRepresentation N) (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (he : ∀ a : Algebra M, τ.norm₂ (e a) = traceTwoNorm σ a)
    (R : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K))
    (hR : ∀ T, ‖R T‖ ≤ ‖T‖) (hRa : ∀ a : Algebra M, R a.val = (e a).val)
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    IsInjective (FiniteMatrixStage.generatedVonNeumann A) := by
  have hξ : τ.vector ≠ 0 := by
    intro h
    have ht := τ.norm_vector
    rw [h,norm_zero] at ht
    exact zero_ne_one ht
  let : Nontrivial K := ⟨⟨τ.vector,0,hξ⟩⟩
  let S (n : ℕ) : (H →L[ℂ] H) →L[ℂ]
      Algebra (matrixUnitConcreteAlgebra (A n).units) := by
    letI : Nonempty (Fin (A n).size) := ⟨⟨0,(A n).positive⟩⟩
    exact transferredMatrixRetraction (A n).units e τ R hR ⟨0,(A n).positive⟩
  let G (n : ℕ) : (H →L[ℂ] H) →ₗ[ℂ] Algebra M :=
    (coordinateInclusion (matrixUnitConcreteAlgebra_le (A n).units)).toAlgHom.toLinearMap.comp
      (S n).toLinearMap
  let F (n : ℕ) : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
    (matrixUnitConcreteAlgebra (A n).units).toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL.comp
      (S n)
  have hG (n : ℕ) (a : Algebra M) : e (G n a.val) =
      conditionalExpectation τ
        (matrixUnitConcreteAlgebra_le ((A n).units.map e.toStarAlgHom)) (e a) := by
    let : Nonempty (Fin (A n).size) := ⟨⟨0,(A n).positive⟩⟩
    exact transferredMatrixRetraction_expectation (A n).units e τ R hR
      ⟨0,(A n).positive⟩ hRa a
  have hGnorm (n : ℕ) (a : Algebra M) :
      traceTwoNorm σ (G n a.val) ≤ traceTwoNorm σ a := by
    rw [← he, hG, ← he]
    exact conditionalExpectation_norm₂_le τ _ _
  have hGfix (n : ℕ) (a : Algebra M) (ha : a.val ∈ (A n).units.concreteAlgebra) :
      G n a.val = a := by
    exact e.injective ((hG n a).trans (conditionalExpectation_fixed τ _ (e a)
      ((mem_mapped_matrix_concrete (A n).units e a).mpr ha)))
  have hSnorm (n : ℕ) : ‖S n‖ ≤ 1 := by
    let : Nonempty (Fin (A n).size) := ⟨⟨0,(A n).positive⟩⟩
    exact transferredMatrixRetraction_norm (A n).units e τ R hR ⟨0,(A n).positive⟩
  refine isInjective_of_finiteTrace_approximations
    (FiniteMatrixStage.generatedVonNeumann_le A) σ hσ F ?_ ?_ ?_
  · intro n
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro T
    exact (S n).le_of_opNorm_le (hSnorm n) T
  · intro n T
    exact FiniteMatrixStage.stage_le_generated A n (S n T).property
  · intro x
    let a : Algebra M := coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le A) x
    change Tendsto (fun n => traceTwoNorm σ (G n a.val - a)) atTop (𝓝 0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k,b,hb,happrox⟩ := hσ.matrix_stage_approximation A hA a x.property (half_pos hε)
    refine ⟨k,fun n hn => ?_⟩
    have hfixed : G n b.val = b := hGfix n b (hA hn hb)
    have hsub : G n (a - b).val = G n a.val - b := by
      change G n (a.val - b.val) = _
      rw [map_sub,hfixed]
    have hdecomp : G n a.val - a = G n (a - b).val - (a - b) := by rw [hsub]; abel
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (traceTwoNorm_nonneg σ _)]
    rw [hdecomp, sub_eq_add_neg]
    have hneg : traceTwoNorm σ (-(a - b)) = traceTwoNorm σ (a - b) := by
      simp only [traceTwoNorm, star_neg, neg_mul, mul_neg, neg_neg]
    have hbnd := (traceTwoNorm_add_le σ (G n (a - b).val) (-(a - b))).trans
      (add_le_add (hGnorm n (a - b)) (le_of_eq hneg))
    linarith

variable (hM : IsII1Factor M.toStarSubalgebra)

include hM in
/-- The original representation of any increasing matrix closure in a finite factor is injective. -/
theorem isInjective_original_matrix_closure
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    IsInjective (FiniteMatrixStage.generatedVonNeumann A) := by
  let T := traceFreeHilbertClosure (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)
  let τ := traceFreeHilbertClosureTrace (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)
  let e : Algebra M ≃⋆ₐ[ℂ] Algebra T := traceFreeHilbertEquiv (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)
  obtain ⟨R,hR,hRa⟩ := exists_traceFreeAmbientExtension (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)
  apply isInjective_matrix_closure_of_trace_extension
    (concreteFactorTrace hM) (concreteFactorTrace_finiteVector hM) τ e _ R hR hRa A hA
  intro a
  change ‖traceFreeHilbertAction (traceHilbert_factor hM) hM.diffuse hM.finite
    (traceHilbert_nonzero hM) a (traceFreeHilbertVector (traceHilbert_factor hM)
      hM.diffuse hM.finite (traceHilbert_nonzero hM))‖ = _
  rw [traceFreeHilbertAction_vector]
  exact concreteTraceEmbedding_norm hM a

include hM in
/-- The finite-factor proof needs no published increasing-matrix injectivity premise. -/
theorem exists_original_irreducible_injective_subalgebra_proved
    [TopologicalSpace.SeparableSpace H] :
    ∃ (Q : VonNeumannAlgebra H) (hQM : Q ≤ M), IsInjective Q ∧
      (∀ b : Algebra M,
        (∀ q : Algebra Q, coordinateInclusion hQM q * b = b * coordinateInclusion hQM q) →
        ∃ c : ℂ, b = c • (1 : Algebra M)) := by
  obtain ⟨A,hA,_hfd,hirr⟩ := exists_original_irreducible_matrix_algebra hM
  exact ⟨FiniteMatrixStage.generatedVonNeumann A,
    FiniteMatrixStage.generatedVonNeumann_le A, isInjective_original_matrix_closure hM A hA,hirr⟩

end

end KadisonKastler

end OAI
