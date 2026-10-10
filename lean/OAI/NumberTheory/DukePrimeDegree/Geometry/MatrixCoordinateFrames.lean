import OAI.NumberTheory.DukePrimeDegree.Dynamics.KernelVelocityFrames
import OAI.NumberTheory.DukePrimeDegree.Dynamics.VelocityRootProjection
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-!
# Coordinate frames on the actual velocity-rank events

The finite-dimensional recurrence argument uses rectangular matrices with
one natural-number row dimension. Flattening the actual matrix space is
only a linear change of coordinates. On each measurable rank event the
selected velocity frame has independent columns and spans the actual
velocity space; outside that event the rectangular frame is zero.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def matrixCoordinateEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] (Fin (n * n) → ℝ) where
  toFun V q := V (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
  invFun v i j := v (finProdFinEquiv (i, j))
  left_inv V := by
    ext i j
    change V (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = V i j
    rw [Equiv.symm_apply_apply]
  right_inv v := by
    ext q
    change v (finProdFinEquiv (finProdFinEquiv.symm q)) = v q
    rw [Equiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinateVelocityFrame {n : ℕ} (μ : Measure (X n)) (k : ℕ) :
    Matrix (Fin (n * n)) (Fin k) ℝ :=
  Matrix.of (fun q j => if velocityFrameCard μ = k then
    matrixCoordinateEquiv n (velocityFrame μ j) q else 0)

lemma coordinateVelocityFrame_eq {n k : ℕ} (μ : Measure (X n))
    (hk : velocityFrameCard μ = k) :
    coordinateVelocityFrame μ k =
      Matrix.of (fun (q : Fin (n * n)) (j : Fin k) =>
        matrixCoordinateEquiv n (velocityFrame μ j) q) := by
  ext q j
  exact ite_eq_left hk

lemma coordinateVelocityFrame_eq_zero {n k : ℕ} (μ : Measure (X n))
    (hk : velocityFrameCard μ ≠ k) : coordinateVelocityFrame μ k = 0 := by
  ext q j
  exact ite_eq_right hk

theorem coordinateVelocityFrame_linearIndependent {n k : ℕ} (μ : Measure (X n))
    (hk : velocityFrameCard μ = k) :
    LinearIndependent ℝ (coordinateVelocityFrame μ k).col := by
  have h := velocityFrame_linearIndependent μ
  rw [hk] at h
  have hm := h.map_injOn (matrixCoordinateEquiv n).toLinearMap
    (fun _ _ _ _ he => (matrixCoordinateEquiv n).injective he)
  rw [coordinateVelocityFrame_eq μ hk]
  change LinearIndependent ℝ (fun j : Fin k => matrixCoordinateEquiv n (velocityFrame μ j))
  exact hm

theorem coordinateVelocityFrame_span {n k : ℕ} (μ : Measure (X n))
    (hk : velocityFrameCard μ = k) :
    Submodule.span ℝ (Set.range (coordinateVelocityFrame μ k).col) =
      (matrixVelocitySpace (invariantRightSubgroup μ)).map
        (matrixCoordinateEquiv n).toLinearMap := by
  have h := congrArg (fun W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) =>
      W.map (matrixCoordinateEquiv n).toLinearMap) (velocityFrame_span μ)
  rw [hk, Submodule.map_span, ← Set.range_comp] at h
  rw [coordinateVelocityFrame_eq μ hk]
  change Submodule.span ℝ (Set.range
    (fun j : Fin k => matrixCoordinateEquiv n (velocityFrame μ j))) = _
  exact h

theorem measurable_coordinateVelocityFrame_entry
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} [Nonempty (Fin n)]
    (κ : Kernel Z (X n)) [IsMarkovKernel κ]
    (k : ℕ) (q : Fin (n * n)) (j : Fin k) :
    Measurable (fun z => coordinateVelocityFrame (κ z) k q j) := by
  have he : (fun z => coordinateVelocityFrame (κ z) k q j) =
      (fun z => if velocityFrameCard (κ z) = k then
        velocityFrame (κ z) (j : ℕ) (finProdFinEquiv.symm q).1
          (finProdFinEquiv.symm q).2 else (0 : ℝ)) := by
    rfl
  rw [he]
  have hE : MeasurableSet {z | velocityFrameCard (κ z) = k} :=
    measurableSet_eq_fun (measurable_velocityFrameCard κ) measurable_const
  have hv : Measurable (fun z => velocityFrame (κ z) (j : ℕ)
      (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) :=
    (measurable_pi_apply (finProdFinEquiv.symm q).2).comp
      ((measurable_pi_apply (finProdFinEquiv.symm q).1).comp (measurable_velocityFrame κ (j : ℕ)))
  exact Measurable.ite hE hv measurable_const

def matrixCoordinateWeight {n : ℕ} (ell : Fin n → ℝ) (q : Fin (n * n)) : ℝ :=
  Real.exp (ell (finProdFinEquiv.symm q).1 - ell (finProdFinEquiv.symm q).2)

lemma matrixCoordinateWeight_pos {n : ℕ} (ell : Fin n → ℝ) (q : Fin (n * n)) :
    0 < matrixCoordinateWeight ell q := Real.exp_pos _

lemma matrixCoordinateEquiv_diagonal_conjugation {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (V : Matrix (Fin n) (Fin n) ℝ) :
    matrixCoordinateEquiv n
        ((diagonalOneParameter ell hell 1).val * V *
          (diagonalOneParameter ell hell (-1)).val) =
      Matrix.diagonal (matrixCoordinateWeight ell) *ᵥ matrixCoordinateEquiv n V := by
  ext q
  change ((diagonalOneParameter ell hell 1).val * V *
      (diagonalOneParameter ell hell (-1)).val)
      (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 = _
  rw [diagonal_matrix_conjugation_entry, Matrix.mulVec_diagonal, mul_one]
  rfl

end DukePrimeDegree

end

end OAI
