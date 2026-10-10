import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace OAI

/-! # Cyclic Hilbert identifications from matching finite Gram matrices

The pointed matrix-product reindexing identifies finite word vectors.
That identification extends from their dense linear spans to the Hilbert spaces.
-/

namespace KadisonKastler

noncomputable section

variable {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
theorem norm_linearCombination_eq_of_gram (v : I → H) (w : I → K)
    (h : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j)) (c : I →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ v c‖ = ‖Finsupp.linearCombination ℂ w c‖ := by
  have hi : inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v c) =
      inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w c) := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
      inner_smul_left, inner_smul_right, h]
  have hs : ‖Finsupp.linearCombination ℂ v c‖ ^ 2 =
      ‖Finsupp.linearCombination ℂ w c‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg Complex.re hi
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

/-- The Hilbert-space identification of two dense families with identical
Gram matrices, including the prescribed action on each family vector. -/
def cyclicGramEquivalence (v : I → H) (w : I → K)
    (hv : DenseRange (Finsupp.linearCombination ℂ v))
    (hw : DenseRange (Finsupp.linearCombination ℂ w))
    (h : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j)) : H ≃ₗᵢ[ℂ] K :=
  (LinearEquiv.refl ℂ (I →₀ ℂ)).extendOfIsometry
    (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w) hv hw
    (fun c => (norm_linearCombination_eq_of_gram v w h c).symm)

theorem cyclicGramEquivalence_linearCombination (v : I → H) (w : I → K)
    (hv : DenseRange (Finsupp.linearCombination ℂ v))
    (hw : DenseRange (Finsupp.linearCombination ℂ w))
    (h : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j)) (c : I →₀ ℂ) :
    cyclicGramEquivalence v w hv hw h (Finsupp.linearCombination ℂ v c) =
      Finsupp.linearCombination ℂ w c :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ c

theorem cyclicGramEquivalence_apply (v : I → H) (w : I → K)
    (hv : DenseRange (Finsupp.linearCombination ℂ v))
    (hw : DenseRange (Finsupp.linearCombination ℂ w))
    (h : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j)) (i : I) :
    cyclicGramEquivalence v w hv hw h (v i) = w i := by
  simpa only [Finsupp.linearCombination_single, one_smul] using
    cyclicGramEquivalence_linearCombination v w hv hw h (Finsupp.single i 1)

end

end KadisonKastler

end OAI
