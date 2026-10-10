import OAI.Analysis.KadisonKastler.RowVectorEstimate
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace OAI

/-! Completing a finite row by the square root of its missing mass. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

section Algebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
def rowSquare {n : ℕ} (r : Fin n → A) : A := ∑ i, r i * star (r i)

theorem rowSquare_nonneg {n : ℕ} (r : Fin n → A) : 0 ≤ rowSquare r :=
  Finset.sum_nonneg fun i _ => mul_star_self_nonneg (r i)

def rowRemainder {n : ℕ} (r : Fin n → A) : A := CFC.sqrt (1 - rowSquare r)

theorem rowRemainder_star {n : ℕ} (r : Fin n → A) : star (rowRemainder r) = rowRemainder r :=
  (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq

theorem rowRemainder_square {n : ℕ} (r : Fin n → A) (hr : rowSquare r ≤ 1) :
    rowRemainder r * rowRemainder r = 1 - rowSquare r :=
  CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hr)

theorem rowRemainder_norm_le {n : ℕ} (r : Fin n → A) (hr : rowSquare r ≤ 1) :
    ‖rowRemainder r‖ ≤ 1 := by
  have hp := sub_nonneg.mpr hr
  have hs : 1 - rowSquare r ≤ 1 := sub_le_self _ (rowSquare_nonneg r)
  have hn : ‖1 - rowSquare r‖ ≤ 1 :=
    (CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one hp).2 (by simpa using hs)
  have he : ‖rowRemainder r‖ * ‖rowRemainder r‖ = ‖1 - rowSquare r‖ := by
    rw [← CStarRing.norm_star_mul_self, rowRemainder_star, rowRemainder_square r hr]
  nlinarith [norm_nonneg (rowRemainder r)]

def completedRow {n : ℕ} (r : Fin n → A) : Fin (n + 1) → A :=
  Fin.cases (rowRemainder r) r

theorem completedRow_normalized {n : ℕ} (r : Fin n → A) (hr : rowSquare r ≤ 1) :
    ∑ i, completedRow r i * star (completedRow r i) = 1 := by
  simp only [completedRow, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
  rw [rowRemainder_star, rowRemainder_square r hr]
  change (1 - rowSquare r) + rowSquare r = 1
  abel

theorem completedRow_average {n : ℕ} (r : Fin n → A) (F : A →ₗ[ℂ] A) (x : A) :
    finiteRightAverage (completedRow r) F x =
      F (x * rowRemainder r) * rowRemainder r + finiteRightAverage r F x := by
  simp only [finiteRightAverage_apply, completedRow, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, rowRemainder_star]

end Algebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance completedRowAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance completedRowAlgebraPreorder (M : VonNeumannAlgebra H) : Preorder (Algebra M) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance completedRowAlgebraLE (M : VonNeumannAlgebra H) : LE (Algebra M) :=
  (CStarAlgebra.spectralOrder _).toLE
local instance completedRowAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem rowRemainder_apply_norm_sq {M : VonNeumannAlgebra H} {n : ℕ}
    (r : Fin n → Algebra M) (hr : rowSquare r ≤ 1) (ξ : H) :
    ‖((rowRemainder r : Algebra M) : H →L[ℂ] H) ξ‖ ^ 2 =
      (inner ℂ ξ (((1 - rowSquare r : Algebra M) : H →L[ℂ] H) ξ)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  have he : inner ℂ (((rowRemainder r : Algebra M) : H →L[ℂ] H) ξ)
      (((rowRemainder r : Algebra M) : H →L[ℂ] H) ξ) =
      inner ℂ ξ (((rowRemainder r * rowRemainder r : Algebra M) : H →L[ℂ] H) ξ) := by
    have h := ContinuousLinearMap.adjoint_inner_right
      ((rowRemainder r : Algebra M) : H →L[ℂ] H) ξ (((rowRemainder r : Algebra M) : H →L[ℂ] H) ξ)
    simpa only [← ContinuousLinearMap.star_eq_adjoint, ← StarMemClass.coe_star,
      rowRemainder_star, MulMemClass.coe_mul, mul_apply_eq_comp] using h.symm
  rw [he, rowRemainder_square r hr]
  rfl

theorem completedRow_average_error {M : VonNeumannAlgebra H} {n : ℕ}
    (r : Fin n → Algebra M) (hr : rowSquare r ≤ 1)
    {F : Algebra M →ₗ[ℂ] Algebra M} {c : ℝ} (hF : CompletelyBoundedBy F c) (hc : 0 ≤ c)
    (x : Algebra M) (ξ : H) :
    ‖((finiteRightAverage (completedRow r) F x - finiteRightAverage r F x : Algebra M) :
      H →L[ℂ] H) ξ‖ ≤ c * ‖x‖ * ‖((rowRemainder r : Algebra M) : H →L[ℂ] H) ξ‖ := by
  rw [completedRow_average, add_sub_cancel_right]
  change ‖(F (x * rowRemainder r) : H →L[ℂ] H)
    (((rowRemainder r : Algebra M) : H →L[ℂ] H) ξ)‖ ≤ _
  calc
    _ ≤ ‖F (x * rowRemainder r)‖ * ‖((rowRemainder r : Algebra M) : H →L[ℂ] H) ξ‖ :=
      (F (x * rowRemainder r) : H →L[ℂ] H).le_opNorm _
    _ ≤ (c * (‖x‖ * ‖rowRemainder r‖)) * ‖((rowRemainder r : Algebra M) : H →L[ℂ] H) ξ‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (hF.apply_norm_le _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) hc)
    _ ≤ c * ‖x‖ * ‖((rowRemainder r : Algebra M) : H →L[ℂ] H) ξ‖ := by
      calc
        _ ≤ (c * (‖x‖ * 1)) * ‖((rowRemainder r : Algebra M) : H →L[ℂ] H) ξ‖ := by
          gcongr
          exact rowRemainder_norm_le r hr
        _ = _ := by ring

end

end KadisonKastler

end OAI
