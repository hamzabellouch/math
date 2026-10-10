import OAI.Analysis.KadisonKastler.RowReplication
import OAI.Analysis.KadisonKastler.RectangularOperator
import OAI.Analysis.KadisonKastler.CompleteWeakLimits

namespace OAI

/-! Vector estimates for truncating the countable rows in module averaging. -/

namespace KadisonKastler

noncomputable section

open Generator
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance rowVectorAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance rowVectorAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance rowVectorOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance rowVectorOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

def algebraRow {M : VonNeumannAlgebra H} {ι : Type*} (r : ι → Algebra M) :
    CStarMatrix (Fin 1) ι (Algebra M) := CStarMatrix.ofMatrix fun _ j => r j

@[simp] theorem algebraRow_apply {M : VonNeumannAlgebra H} {ι : Type*}
    (r : ι → Algebra M) (i : Fin 1) (j : ι) : algebraRow r i j = r j := rfl

def rowAdjointVector {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (ξ : H) : FiniteHilbert ι H :=
  WithLp.toLp 2 fun i => (star (r i) : H →L[ℂ] H) ξ

theorem rowAdjointVector_norm_sq {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (ξ : H) :
    ‖rowAdjointVector r ξ‖ ^ 2 =
      (inner ℂ ξ (((∑ i, r i * star (r i) : Algebra M) : H →L[ℂ] H) ξ)).re := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i, ‖(star (r i) : H →L[ℂ] H) ξ‖ ^ 2) = _
  have hcoe : ((∑ i, r i * star (r i) : Algebra M) : H →L[ℂ] H) =
      ∑ i, (r i : H →L[ℂ] H) * star (r i : H →L[ℂ] H) := by simp
  rw [hcoe]
  simp only [norm_sq_eq_re_inner (𝕜 := ℂ), sum_apply, inner_sum]
  change (∑ i, (inner ℂ ((star (r i) : H →L[ℂ] H) ξ)
    ((star (r i) : H →L[ℂ] H) ξ)).re) =
    Complex.reCLM (∑ i, inner ℂ ξ (((r i : H →L[ℂ] H) * star (r i : H →L[ℂ] H)) ξ))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_apply_eq_comp]
  simpa only [← ContinuousLinearMap.star_eq_adjoint, star_star, Complex.reCLM_apply] using
    congrArg Complex.re (ContinuousLinearMap.adjoint_inner_right
      (star (r i : H →L[ℂ] H)) ξ ((star (r i : H →L[ℂ] H)) ξ)).symm

/-- The tail is controlled by the adjoint row on the chosen vector, even
when the completely bounded map is not normal. -/
theorem finiteRightAverage_vector_bound {M : VonNeumannAlgebra H}
    {n : ℕ} (r : Fin n → Algebra M)
    {F : Algebra M →ₗ[ℂ] Algebra M} {c : ℝ}
    (hF : CompletelyBoundedBy F c) (hc : 0 ≤ c) (x : Algebra M) (ξ : H) :
    ‖(finiteRightAverage r F x : H →L[ℂ] H) ξ‖ ≤
      c * ‖x‖ * ‖algebraRow r‖ * ‖rowAdjointVector r ξ‖ := by
  classical
  let e := M.toStarSubalgebra.subtype
  let X := scalarMatrixCopy x * algebraRow r
  let Y := CStarMatrix.mapₗ e.toAlgHom.toLinearMap (CStarMatrix.mapₗ F X)
  have hX : ∀ i j, X i j = x * r j := by
    intro i j
    fin_cases i
    simp [X, CStarMatrix.mul_apply, scalarMatrixCopy_apply]
  have he := injective_starAlgHom_completelyIsometric e Subtype.val_injective
  have hY : ‖Y‖ ≤ c * ‖x‖ * ‖algebraRow r‖ := by
    change ‖CStarMatrix.mapₗ e.toAlgHom.toLinearMap (CStarMatrix.mapₗ F X)‖ ≤ _
    rw [he 1 n]
    exact (hF.finite X).trans (by
      have hb := rectangular_norm_mul_le_finite (scalarMatrixCopy x) (algebraRow r)
      rw [scalarMatrixCopy_norm] at hb
      exact (mul_le_mul_of_nonneg_left hb hc).trans_eq (by ring))
  have hv : rectangularHilbertMatrix Y (rowAdjointVector r ξ) =
      tupleSingle 0 ((finiteRightAverage r F x : H →L[ℂ] H) ξ) := by
    ext i
    fin_cases i
    simp only [rectangularHilbertMatrix_apply, tupleSingle_apply]
    change (∑ j, (F (X 0 j) : H →L[ℂ] H) ((star (r j) : H →L[ℂ] H) ξ)) =
      (finiteRightAverage r F x : H →L[ℂ] H) ξ
    simp_rw [hX]
    simp [finiteRightAverage_apply]

  have h := (rectangularHilbertMatrix Y).le_opNorm (rowAdjointVector r ξ)
  rw [hv, norm_tupleSingle, norm_rectangularHilbertMatrix] at h
  exact h.trans (mul_le_mul_of_nonneg_right hY (norm_nonneg _))

end

end KadisonKastler

end OAI
