import OAI.NumberTheory.DukePrimeDegree.Geometry.FrameWeightRigidity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace OAI

/-!
# Diagonal invariance of an actual frame

A nonzero pivot minor gives a concrete normalized frame, by multiplying
on the right by that minor's inverse.  The one-weight conclusion for
the original minors then makes its column space diagonal-invariant.
The pivot may be chosen separately at each point; no invariant chart
or measurable choice of the pivot is assumed.
-/

noncomputable section
open MeasureTheory Filter Matrix Set
open scoped BigOperators

namespace DukePrimeDegree

lemma frame_submatrix_mul_right {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (R : Matrix (Fin k) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) :
    (B * R).submatrix p id = B.submatrix p id * R := by
  ext i j
  rfl

lemma frameMinor_mul_right {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (R : Matrix (Fin k) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) :
    frameMinor (B * R) p = frameMinor B p * R.det := by
  unfold frameMinor
  rw [frame_submatrix_mul_right, Matrix.det_mul]

def normalizeFrame {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) : Matrix (Fin n) (Fin k) ℝ :=
  B * (B.submatrix p id)⁻¹

lemma normalizeFrame_pivot {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) (hp : frameMinor B p ≠ 0) :
    (normalizeFrame B p).submatrix p id = 1 := by
  rw [normalizeFrame, frame_submatrix_mul_right]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp)

lemma normalizeFrame_mul_pivot {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) (hp : frameMinor B p ≠ 0) :
    normalizeFrame B p * B.submatrix p id = B := by
  exact Matrix.nonsing_inv_mul_cancel_right _ B (isUnit_iff_ne_zero.mpr hp)

/-- The change of basis exhibiting invariance is the explicit conjugate
of the diagonal on the pivot rows. -/
theorem diagonal_mul_frame_of_minor_weights {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (p : Fin k ↪ Fin n)
    (hp : frameMinor B p ≠ 0)
    (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0)
    (hminor : ∀ q, (∏ u, a (q u)) ≠ ∏ u, a (p u) → frameMinor B q = 0) :
    Matrix.diagonal a * B = B *
      ((B.submatrix p id)⁻¹ * Matrix.diagonal (fun u => a (p u)) * B.submatrix p id) := by
  have hnormalized : Matrix.diagonal a * normalizeFrame B p =
      normalizeFrame B p * Matrix.diagonal (fun u => a (p u)) := by
    apply diagonal_mul_frame_eq_frame_mul_diagonal _ p (normalizeFrame_pivot B p hp) a ha
    intro q hq
    rw [normalizeFrame, frameMinor_mul_right, hminor q hq, zero_mul]
  calc
    Matrix.diagonal a * B = Matrix.diagonal a *
        (normalizeFrame B p * B.submatrix p id) := by
          rw [normalizeFrame_mul_pivot B p hp]
    _ = normalizeFrame B p * Matrix.diagonal (fun u => a (p u)) *
        B.submatrix p id := by rw [← Matrix.mul_assoc, hnormalized]
    _ = _ := by simp only [normalizeFrame, Matrix.mul_assoc]

/-- A finite invariant law of actual full-rank frames is supported on
diagonal-invariant column spaces. This derives the invariant-space
conclusion from frame covariance, without assuming a fixed pivot chart. -/
theorem ae_frame_diagonal_invariant
    {Y : Type*} [MeasurableSpace Y] {n k : ℕ}
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (B : Y → Matrix (Fin n) (Fin k) ℝ)
    (hB : ∀ i j, Measurable (fun x => B x i j))
    (hfull : ∀ᵐ x ∂μ, ∃ p : Fin k ↪ Fin n, frameMinor (B x) p ≠ 0)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (R : Y → Matrix (Fin k) (Fin k) ℝ)
    (hR : ∀ᵐ x ∂μ, (R x).det ≠ 0)
    (hcov : ∀ᵐ x ∂μ, B (T x) = Matrix.diagonal a * B x * R x) :
    ∀ᵐ x ∂μ, ∃ C : Matrix (Fin k) (Fin k) ℝ,
      Matrix.diagonal a * B x = B x * C := by
  filter_upwards [hfull,
    ae_frame_minors_have_one_diagonal_weight μ T hT B hB a ha R hR hcov]
    with x hx hweights
  obtain ⟨p, hp⟩ := hx
  refine ⟨((B x).submatrix p id)⁻¹ *
    Matrix.diagonal (fun u => a (p u)) * (B x).submatrix p id, ?_⟩
  apply diagonal_mul_frame_of_minor_weights (B x) p hp a (fun i => ne_of_gt (ha i))
  intro q hq
  exact (hweights q p hq).resolve_right hp

end DukePrimeDegree

end

end OAI
