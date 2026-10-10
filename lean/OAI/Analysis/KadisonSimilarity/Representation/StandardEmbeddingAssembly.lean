import OAI.Analysis.KadisonSimilarity.Derivation.CountableCyclicDecomposition
import OAI.Analysis.KadisonSimilarity.Representation.CountableAmplification

namespace OAI

/-! Assemble embeddings of the cyclic summands into the countable standard
representation. The countability and Hilbert-sum construction are proved;
only the embeddings of the individual cyclic representations are parameters. -/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace CyclicDecompositionData

variable {N : StarSubalgebra ℂ (H →L[ℂ] H)} (D : CyclicDecompositionData N)

/-- The actual total orthogonal cyclic family is a Hilbert direct sum. -/
theorem isHilbertSum : IsHilbertSum ℂ D.Space D.summands.inclusion := by
  apply IsHilbertSum.mk D.summands.orthogonal
  have heq : (⨆ i, LinearMap.range (D.summands.inclusion i).toLinearMap) =
      Submodule.span ℂ (⋃ i, Set.range (D.summands.inclusion i)) := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      rintro x ⟨y, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, y, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      intro x hx
      obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
      exact Submodule.mem_iSup_of_mem i ⟨y, rfl⟩
  rw [heq, D.summands.dense_span]

end CyclicDecompositionData

omit [CompleteSpace K] in
private def countableSingleIsometry (n : ℕ) : K →ₗᵢ[ℂ] CountableCopies K where
  toLinearMap := (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => K) 2 n).toLinearMap
  norm_map' x := by
    change ‖lp.single (E := fun _ : ℕ => K) 2 n x‖ = ‖x‖
    exact lp.norm_single (p := 2) (E := fun _ : ℕ => K) (by norm_num) n x

omit [CompleteSpace K] in
private theorem countableAmplify_single (T : K →L[ℂ] K) (n : ℕ) (x : K) :
    countableAmplify T (lp.single 2 n x) = lp.single 2 n (T x) := by
  ext j
  simp only [countableAmplify_apply, lp.single_apply, Pi.single_apply]
  split_ifs <;> simp only [map_zero]

/-- Countably many cyclic intertwiners combine into one isometric
intertwiner on the original separable representation. -/
theorem countable_embedding_of_cyclic_embeddings
    [TopologicalSpace.SeparableSpace H]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (D : CyclicDecompositionData σ.range)
    (J : ∀ i, D.Space i →ₗᵢ[ℂ] K)
    (hJ : ∀ i a, (J i).toContinuousLinearMap.comp (D.representation σ i a) =
      (ρ a).comp (J i).toContinuousLinearMap) :
    ∃ I : H →ₗᵢ[ℂ] CountableCopies K,
      ∀ a, I.toContinuousLinearMap.comp (σ a) =
        (countableAmplify (ρ a)).comp I.toContinuousLinearMap := by
  classical
  let := D.generators_countable
  obtain ⟨f, hf⟩ := exists_injective_nat D.generators
  let W : ∀ i, D.Space i →ₗᵢ[ℂ] CountableCopies K := fun i =>
    (countableSingleIsometry (f i)).comp (J i)
  have hW : OrthogonalFamily ℂ D.Space W := by
    intro i j hij x y
    change inner ℂ (lp.single (E := fun _ : ℕ => K) 2 (f i) (J i x))
      (lp.single (E := fun _ : ℕ => K) 2 (f j) (J j y)) = 0
    rw [lp.inner_single_left]
    simp only [lp.single_apply, Pi.single_apply, hf.ne hij, ite_false, inner_zero_right]
  let E := D.isHilbertSum.linearIsometryEquiv
  let I := hW.linearIsometry.comp E.toLinearIsometry
  have hI (i : D.generators) (x : D.Space i) :
      I (D.summands.inclusion i x) = lp.single 2 (f i) (J i x) := by
    have hE : E (D.summands.inclusion i x) = lp.single 2 i x := by
      apply E.symm.injective
      rw [E.symm_apply_apply]
      exact (D.isHilbertSum.linearIsometryEquiv_symm_apply_single x).symm
    change hW.linearIsometry (E (D.summands.inclusion i x)) = _
    rw [hE, hW.linearIsometry_apply_single]
    rfl
  refine ⟨I, fun a => ?_⟩
  have hdense : Dense (Submodule.span ℂ (⋃ i, Set.range (D.summands.inclusion i)) : Set H) := by
    intro x
    change x ∈ (Submodule.span ℂ (⋃ i, Set.range (D.summands.inclusion i))).topologicalClosure
    rw [D.summands.dense_span]
    trivial
  apply ContinuousLinearMap.ext_on hdense
  intro x hx
  obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
  have hσ := congrArg (fun T => T y) (D.representation_intertwines σ i a)
  have hj := congrArg (fun T => T y) (hJ i a)
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap] at hσ hj ⊢
  rw [hσ, hI, hI, countableAmplify_single, hj]

end KadisonSimilarity

end

end OAI
