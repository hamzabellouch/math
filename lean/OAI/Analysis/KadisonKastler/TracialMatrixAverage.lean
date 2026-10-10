import OAI.Analysis.KadisonKastler.MatrixStateAveraging
import OAI.Analysis.KadisonKastler.MatrixOrbitAverage
import OAI.Analysis.FactorGeneration.GroupTrace

namespace OAI

/-! # Exact scalar values of finite matrix averages in a tracial algebra -/

namespace KadisonKastler

open Generator UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

/-- On the matrix algebra, finite signed averaging is exactly the scalar
specified by the represented trace. -/
theorem tracial_matrixUnitAverage_eq_trace (τ : TracialRepresentation M)
    {n : ℕ} [Nonempty (Fin n)] (E : MatrixUnitSystem (Fin n) (H →L[ℂ] H))
    (hE : E.algebra ≤ M.toStarSubalgebra) (x : Algebra M) (hx : x.val ∈ E.algebra) :
    matrixUnitAverage E x.val = τ.trace x • (1 : H →L[ℂ] H) := by
  obtain ⟨z, hz⟩ := matrixUnitAverage_scalar E x.val hx
  have hc : ∀ a ∈ E.algebra, ∀ y ∈ M,
      inner ℂ τ.vector ((a * y) τ.vector) = inner ℂ τ.vector ((y * a) τ.vector) := by
    intro a ha y hy
    exact τ.cyclic ⟨a, hE ha⟩ ⟨y, hy⟩
  have ht := matrixUnitAverage_preserves_vectorFunctional M τ.vector E hE hc x.val x.property
  have hzt : z = τ.trace x := by
    rw [hz] at ht
    change inner ℂ τ.vector ((z • (1 : H →L[ℂ] H)) τ.vector) = τ.trace x at ht
    have hn : inner ℂ τ.vector τ.vector = 1 := by
      simpa only [TracialRepresentation.trace, OneMemClass.coe_one, one_apply_eq_self] using τ.trace_one
    simpa only [smul_apply, one_apply_eq_self, inner_smul_right, hn, mul_one] using ht
  rwa [hzt] at hz

end

end KadisonKastler

end OAI
