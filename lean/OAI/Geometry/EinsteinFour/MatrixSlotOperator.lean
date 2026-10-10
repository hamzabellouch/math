import OAI.Geometry.EinsteinFour.MetricHessian
import OAI.Geometry.EinsteinFour.GradientProjection
import OAI.Geometry.EinsteinFour.GradientPairing
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace OAI

/-! The varying matrix-slot curvature coefficient as an actual bounded
operator. The extension to all matrix arrays is self-adjoint; on trace-free
arrays it is the trace-free anticommutator used in the Weyl equation. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

local instance : NormedAddCommGroup Mat := Matrix.frobeniusNormedAddCommGroup
local instance : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace

private def matrixEntryKernel (A : Mat) (p q : Fin 3 × Fin 3) : ℝ :=
  (1 / 2 : ℝ) * ((if p.2 = q.2 then A p.1 q.1 else 0) +
    (if p.1 = q.1 then A q.2 p.2 else 0)) -
  (1 / 3 : ℝ) * ((if p.1 = p.2 then A q.2 q.1 else 0) +
    (if q.1 = q.2 then A p.1 p.2 else 0))

def matrixSlotKernel (A : Mat) (p q : GradientIndex) : ℝ :=
  if p.1 = q.1 then matrixEntryKernel A p.2 q.2 else 0

private theorem matrixEntryKernel_add (A B : Mat) (p q : Fin 3 × Fin 3) :
    matrixEntryKernel (A + B) p q = matrixEntryKernel A p q + matrixEntryKernel B p q := by
  unfold matrixEntryKernel
  simp only [Matrix.add_apply]
  split_ifs <;> ring

private theorem matrixEntryKernel_smul (c : ℝ) (A : Mat) (p q : Fin 3 × Fin 3) :
    matrixEntryKernel (c • A) p q = c * matrixEntryKernel A p q := by
  unfold matrixEntryKernel
  simp only [Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

private theorem matrixEntryKernel_symmetric (A : Mat) (hA : symmetric A)
    (p q : Fin 3 × Fin 3) : matrixEntryKernel A p q = matrixEntryKernel A q p := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  unfold matrixEntryKernel
  dsimp only
  rw [hA c a, hA d b, hA d c, hA b a]
  split_ifs <;> simp_all [add_comm]

theorem matrixSlotKernel_add (A B : Mat) (p q : GradientIndex) :
    matrixSlotKernel (A + B) p q = matrixSlotKernel A p q + matrixSlotKernel B p q := by
  unfold matrixSlotKernel
  split_ifs <;> simp only [matrixEntryKernel_add, add_zero]

theorem matrixSlotKernel_smul (c : ℝ) (A : Mat) (p q : GradientIndex) :
    matrixSlotKernel (c • A) p q = c * matrixSlotKernel A p q := by
  unfold matrixSlotKernel
  split_ifs <;> simp only [matrixEntryKernel_smul, mul_zero]

theorem matrixSlotKernel_symmetric (A : Mat) (hA : symmetric A) (p q : GradientIndex) :
    matrixSlotKernel A p q = matrixSlotKernel A q p := by
  unfold matrixSlotKernel
  by_cases h : p.1 = q.1
  · rw [ite_eq_left h, ite_eq_left h.symm]
    exact matrixEntryKernel_symmetric A hA p.2 q.2
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

def matrixSlotLinear (A : Mat) : GradientVector →ₗ[ℝ] GradientVector where
  toFun Z := WithLp.toLp 2 (fun p => ∑ q, matrixSlotKernel A p q * Z q)
  map_add' Z W := by
    ext p
    change (∑ q, matrixSlotKernel A p q * (Z q + W q)) =
      (∑ q, matrixSlotKernel A p q * Z q) + ∑ q, matrixSlotKernel A p q * W q
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' c Z := by
    ext p
    change (∑ q, matrixSlotKernel A p q * (c * Z q)) =
      c * (∑ q, matrixSlotKernel A p q * Z q)
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring

/-- The bounded operator that acts on every matrix slice of the Weyl gradient. -/
def matrixSlotOperator (A : Mat) : GradientVector →L[ℝ] GradientVector :=
  (matrixSlotLinear A).toContinuousLinearMap

theorem matrixSlotOperator_apply (A : Mat) (Z : GradientVector) (p : GradientIndex) :
    matrixSlotOperator A Z p = ∑ q, matrixSlotKernel A p q * Z q := rfl

/-- The full-space extension is self-adjoint for every symmetric coefficient.
Thus operator Green applies to its first derivatives as well. -/
theorem matrixSlotOperator_selfadjoint (A : Mat) (hA : symmetric A)
    (Z W : GradientVector) :
    inner ℝ (matrixSlotOperator A Z) W = inner ℝ Z (matrixSlotOperator A W) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    matrixSlotOperator_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [matrixSlotKernel_symmetric A hA q p]
  ring

def matrixSlotOperatorLinear : Mat →ₗ[ℝ] (GradientVector →L[ℝ] GradientVector) where
  toFun := matrixSlotOperator
  map_add' A B := by
    ext Z p
    change (∑ q, matrixSlotKernel (A + B) p q * Z q) =
      (∑ q, matrixSlotKernel A p q * Z q) + ∑ q, matrixSlotKernel B p q * Z q
    simp only [matrixSlotKernel_add, add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    ext Z p
    change (∑ q, matrixSlotKernel (c • A) p q * Z q) =
      c * (∑ q, matrixSlotKernel A p q * Z q)
    simp only [matrixSlotKernel_smul, mul_assoc, Finset.mul_sum]

/-- Continuous linear dependence on the matrix coefficient. -/
def matrixSlot : Mat →L[ℝ] (GradientVector →L[ℝ] GradientVector) :=
  matrixSlotOperatorLinear.toContinuousLinearMap

@[simp] theorem matrixSlot_apply (A : Mat) : matrixSlot A = matrixSlotOperator A := rfl

/-- Differentiating the varying coefficient commutes with the concrete
matrix-slot construction. -/
theorem hasDerivAt_matrixSlot {T : ℝ → Mat} {dT : Mat} {t : ℝ}
    (hT : HasDerivAt T dT t) :
    HasDerivAt (fun s => matrixSlotOperator (T s)) (matrixSlotOperator dT) t := by
  convert! (matrixSlot.hasFDerivAt.comp_hasDerivAt t hT) using 1

/-- The uncompressed trace-free anticommutator on a matrix. -/
def matrixSlotAction (A M : Mat) : Mat := fun a b =>
  (1 / 2 : ℝ) * ((∑ c, A a c * M c b) + ∑ c, M a c * A c b) -
    if a = b then (∑ c, ∑ d, A c d * M d c) / 3 else 0

theorem matrixSlotAction_diagonal (t : Fin 3 → ℝ) (M : Mat) :
    matrixSlotAction (Matrix.diagonal t) M = diagonalCurvatureAction t M := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [matrixSlotAction, diagonalCurvatureAction, Matrix.diagonal,
      Fin.sum_univ_three]
  all_goals ring

private theorem matrixEntryKernel_action (A M : Mat) (hM : traceFree M)
    (a b : Fin 3) :
    (∑ p : Fin 3 × Fin 3, matrixEntryKernel A (a, b) p * M p.1 p.2) =
      matrixSlotAction A M a b := by
  have ht := hM
  simp only [traceFree, Fin.sum_univ_three] at ht
  have h22 : M 2 2 = -M 0 0 - M 1 1 := by linarith
  fin_cases a <;> fin_cases b <;>
    simp [matrixEntryKernel, matrixSlotAction, Fintype.sum_prod_type, Fin.sum_univ_three, h22]
  all_goals ring

/-- On actual trace-free gradient slices, the bounded operator is precisely
`B_F(A)` rather than an independently postulated coefficient. -/
theorem matrixSlotOperator_on_traceFree (A : Mat) (Z : GradientVector)
    (hZ : ∀ i, (∑ a, Z (i, a, a)) = 0) (i : Fin 4) (a b : Fin 3) :
    matrixSlotOperator A Z (i, a, b) =
      matrixSlotAction A (fun c d => Z (i, c, d)) a b := by
  rw [matrixSlotOperator_apply]
  simp only [matrixSlotKernel, Fintype.sum_prod_type, ite_mul, zero_mul]
  have hs : (∑ j : Fin 4, ∑ c : Fin 3, ∑ d : Fin 3,
      if i = j then matrixEntryKernel A (a, b) (c, d) * Z (j, c, d) else 0) =
      ∑ c : Fin 3, ∑ d : Fin 3, matrixEntryKernel A (a, b) (c, d) * Z (i, c, d) := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp
  rw [hs]
  simpa only [Fintype.sum_prod_type] using
    matrixEntryKernel_action A (fun c d => Z (i, c, d)) (hZ i) a b

end

end PositiveEinsteinFour.Geometry

end OAI
