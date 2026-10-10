import OAI.Analysis.KadisonKastler.TracialMatrixAverage
import OAI.Analysis.KadisonKastler.FiniteOrderAveraging
import OAI.Analysis.KadisonKastler.TypeIIIDixmier

namespace OAI

/-! # Averaging a projection bracketed by finite matrix cuts -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

/-- Two matrix cuts with close real traces give a finite inner average of
the intervening projection close to the lower scalar trace. -/
theorem exists_scalar_average_of_tracial_matrix_bracket (τ : TracialRepresentation M)
    {n : ℕ} [Nonempty (Fin n)] (E : MatrixUnitSystem (Fin n) (H →L[ℂ] H))
    (hE : E.algebra ≤ M.toStarSubalgebra)
    (p q r : AlgebraProjection M) (hq : q.val.val ∈ E.algebra) (hr : r.val.val ∈ E.algebra)
    (α β : ℝ) (hαβ : α ≤ β)
    (hqt : τ.trace q.val = (α : ℂ)) (hrt : τ.trace r.val = (β : ℂ))
    (hqp : q.val.val ≤ p.val.val) (hpr : p.val.val ≤ r.val.val) :
    ∃ A : FiniteInnerAverage M, ‖A.apply p.val.val - (α : ℂ) • (1 : H →L[ℂ] H)‖ ≤ β - α := by
  let A := matrixInnerAverage E hE
  have hqA : A.apply q.val.val = algebraMap ℝ (H →L[ℂ] H) α := by
    change matrixUnitAverage E q.val.val = _
    rw [tracial_matrixUnitAverage_eq_trace τ E hE q.val hq, hqt]
    rw [Algebra.algebraMap_eq_smul_one]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) α (1 : H →L[ℂ] H)).symm
  have hrA : A.apply r.val.val = algebraMap ℝ (H →L[ℂ] H) β := by
    change matrixUnitAverage E r.val.val = _
    rw [tracial_matrixUnitAverage_eq_trace τ E hE r.val hr, hrt]
    rw [Algebra.algebraMap_eq_smul_one]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) β (1 : H →L[ℂ] H)).symm
  refine ⟨A, ?_⟩
  have h := A.norm_apply_sub_scalar_le p.val.val q.val.val r.val.val α β hαβ hqp hpr hqA hrA
  have he : algebraMap ℝ (H →L[ℂ] H) α = (α : ℂ) • (1 : H →L[ℂ] H) := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) α (1 : H →L[ℂ] H)
  rw [he] at h
  exact h

end

end KadisonKastler

end OAI
