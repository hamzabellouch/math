import OAI.Analysis.KadisonKastler.RectangularRowNorm
import OAI.Analysis.KadisonKastler.FiniteRowAverages

namespace OAI

/-! The diagonal replication of a row and the matrix formula for averaging. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq ι]

/-- Place the same row along the diagonal of a rectangular matrix. -/
def rowReplication (r : κ → A) : CStarMatrix ι (ι × κ) A :=
  CStarMatrix.ofMatrix fun i jk => if i = jk.1 then r jk.2 else 0

omit [Fintype ι] [Fintype κ] in
@[simp] theorem rowReplication_apply (r : κ → A) (i : ι) (jk : ι × κ) :
    rowReplication r i jk = if i = jk.1 then r jk.2 else 0 := rfl

/-- Replicating a normalized row gives a coisometry. -/
theorem rowReplication_mul_star (r : κ → A) (hr : ∑ k, r k * star (r k) = 1) :
    rowReplication (ι := ι) r * (rowReplication (ι := ι) r).conjTranspose = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [CStarMatrix.mul_apply, Fintype.sum_prod_type, hr]
  · simp [CStarMatrix.mul_apply, Fintype.sum_prod_type, h, Ne.symm h]

omit [Fintype κ] [Fintype τ] in
/-- Multiplication by the replicated row appends its entries. -/
theorem mul_rowReplication_apply (X : CStarMatrix τ ι A) (r : κ → A)
    (i : τ) (jk : ι × κ) :
    (X * rowReplication (ι := ι) r : CStarMatrix τ (ι × κ) A) i jk = X i jk.1 * r jk.2 := by
  simp [CStarMatrix.mul_apply, mul_ite]

omit [Fintype τ] in
/-- The same row average operates at every matrix level. -/
theorem finiteRightAverage_matrix (r : κ → A) (F : A →ₗ[ℂ] A)
    (X : CStarMatrix τ ι A) :
    CStarMatrix.mapₗ (finiteRightAverage r F) X =
      CStarMatrix.mapₗ F (X * rowReplication r) * (rowReplication r).conjTranspose := by
  ext i j
  change (∑ k, F (X i j * r k) * star (r k)) =
    ∑ jk : ι × κ, F ((X * rowReplication r : CStarMatrix τ (ι × κ) A) i jk) *
      star (rowReplication r j jk)
  simp_rw [mul_rowReplication_apply]
  simp only [Fintype.sum_prod_type, rowReplication_apply]
  simp_rw [apply_ite star, star_zero, mul_ite, mul_zero]
  simp


variable [PartialOrder A] [StarOrderedRing A]

theorem rowReplication_norm_bounds (r : κ → A) (hr : ∑ k, r k * star (r k) = 1) :
    ‖rowReplication (ι := ι) r‖ ≤ 1 ∧ ‖(rowReplication (ι := ι) r).conjTranspose‖ ≤ 1 := by
  apply rectangular_row_and_column_contract
  rw [rowReplication_mul_star r hr]
  have h := CStarRing.norm_star_mul_self (x := (1 : CStarMatrix ι ι A))
  simp only [star_one, one_mul] at h
  nlinarith [norm_nonneg (1 : CStarMatrix ι ι A)]

/-- Finite normalized row averages contract the complete norm. -/
theorem CompletelyBoundedBy.finiteRightAverage {F : A →ₗ[ℂ] A} {c : ℝ}
    (hF : CompletelyBoundedBy F c) (hc : 0 ≤ c)
    (r : κ → A) (hr : ∑ k, r k * star (r k) = 1) :
    CompletelyBoundedBy (finiteRightAverage r F) c := by
  intro p q X
  have hb := rowReplication_norm_bounds (ι := Fin q) r hr
  rw [finiteRightAverage_matrix]
  calc
    _ ≤ ‖CStarMatrix.mapₗ F (X * rowReplication r)‖ * ‖(rowReplication r).conjTranspose‖ :=
      rectangular_norm_mul_le_finite _ _
    _ ≤ (c * (‖X‖ * ‖rowReplication r‖)) * ‖(rowReplication r).conjTranspose‖ := by
      gcongr
      exact (hF.finite _).trans (mul_le_mul_of_nonneg_left (rectangular_norm_mul_le_finite _ _) hc)
    _ ≤ c * ‖X‖ := by
      calc
        _ ≤ (c * (‖X‖ * 1)) * 1 := by gcongr; exacts [hb.1, hb.2]
        _ = _ := by ring

end

end KadisonKastler

end OAI
