import OAI.Analysis.KadisonKastler.MatrixEmbedding
import OAI.Analysis.FactorGeneration.NormalDimension

namespace OAI

/-! # Full matrix subalgebras of every finite size in a II₁ factor

The existing continuous-dimension construction gives an equivalent
partition of the identity of every positive finite size. Its displayed
partial-isometry legs give the required actual matrix units.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Every positive finite matrix size occurs unitally inside the factor. -/
theorem exists_matrixUnits_of_size (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (k : ℕ) (hk : 0 < k) :
    Nonempty (Generator.MatrixUnitSystem (Fin k) (Algebra M)) := by
  have hc : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
    intro c hc
    obtain ⟨z, hz⟩ := hM.factor c hc
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  have hunit : (1 : Algebra M) ≠ 0 := by
    intro h
    exact hM.nonzero (congrArg Subtype.val h).symm
  obtain ⟨E⟩ := Generator.Tracial.traceFreeDimension_exists_equivalent_partition
    hc hM.diffuse hM.finite hunit k hk
      (⟨1, IsStarProjection.one (Algebra M)⟩ : Generator.Tracial.AlgebraProjection M)
  exact ⟨E.matrixUnits rfl⟩

/-- Fixed choices of the `(j+1)`-dimensional coordinate matrix algebras. -/
def factorMatrixUnits (hM : Generator.IsII1Factor M.toStarSubalgebra) (j : ℕ) :
    Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M) :=
  Classical.choice (exists_matrixUnits_of_size hM (j + 1) (Nat.zero_lt_succ j))

/-- Every diagonal coordinate has the required normalized trace. -/
theorem factorMatrixUnits_trace_diagonal (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τ : FaithfulTracialState (Algebra M)) (j : ℕ) (i : Fin (j + 1)) :
    τ.toLinearMap ((factorMatrixUnits hM j).entry i i) = ((j + 1 : ℕ) : ℂ)⁻¹ := by
  simpa only [Fintype.card_fin] using matrixUnits_trace_diagonal (factorMatrixUnits hM j) τ i

end

end KadisonKastler

end OAI
