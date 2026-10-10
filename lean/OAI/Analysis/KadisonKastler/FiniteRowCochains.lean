import OAI.Analysis.KadisonKastler.RowReplication
import OAI.Analysis.KadisonKastler.FiniteHaagerupBounds

namespace OAI

/-! Complete norm bounds for the finite cochain averages. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq ι]

omit [Fintype κ] [Fintype τ] in
theorem finiteBilinearProduct_rowReplication_apply (f : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (X : CStarMatrix τ ι A) (r : κ → A) (i : τ) (jk : ι × κ) :
    finiteBilinearProduct f X (rowReplication r) i jk = f (X i jk.1) (r jk.2) := by
  change (∑ j, f (X i j) (if j = jk.1 then r jk.2 else 0)) = _
  simp [apply_ite]

omit [Fintype τ] in
/-- The cochain average at a matrix is a bilinear amplification followed by
multiplication with the adjoint of the replicated row. -/
theorem finiteCochainAverage_matrix (r : κ → A) (f : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (X : CStarMatrix τ ι A) :
    CStarMatrix.mapₗ (finiteCochainAverage r f) X =
      finiteBilinearProduct f X (rowReplication r) * (rowReplication r).conjTranspose := by
  ext i j
  change (∑ k, f (X i j) (r k) * star (r k)) =
    ∑ jk : ι × κ, finiteBilinearProduct f X (rowReplication r) i jk *
      star (rowReplication r j jk)
  simp_rw [finiteBilinearProduct_rowReplication_apply]
  simp only [Fintype.sum_prod_type, rowReplication_apply]
  simp_rw [apply_ite star, star_zero, mul_ite, mul_zero]
  simp

variable [PartialOrder A] [StarOrderedRing A]

/-- A normalized row produces a linear cochain with no loss of complete norm. -/
theorem HaagerupBound.finiteCochainAverage {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ}
    (hf : HaagerupBound f c) (hc : 0 ≤ c)
    (r : κ → A) (hr : ∑ k, r k * star (r k) = 1) :
    CompletelyBoundedBy (finiteCochainAverage r f) c := by
  intro p q X
  have hb := rowReplication_norm_bounds (ι := Fin q) r hr
  rw [finiteCochainAverage_matrix]
  calc
    _ ≤ ‖finiteBilinearProduct f X (rowReplication r)‖ * ‖(rowReplication r).conjTranspose‖ :=
      rectangular_norm_mul_le_finite _ _
    _ ≤ (c * ‖X‖ * ‖rowReplication r‖) * ‖(rowReplication r).conjTranspose‖ := by
      exact mul_le_mul_of_nonneg_right (hf.finite _ _) (norm_nonneg _)
    _ ≤ c * ‖X‖ := by
      calc
        _ ≤ (c * ‖X‖ * 1) * 1 := by gcongr; exacts [hb.1, hb.2]
        _ = _ := by ring

end

end KadisonKastler

end OAI
