import OAI.NumberTheory.DukePrimeDegree.Dynamics.DiagonalProjectiveRecurrence
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Matrix.MeasurableSpace

namespace OAI

/-!
# Actual frame minors under diagonal transport

The projective coordinates here are determinants of minors of an actual
real matrix frame. Changing its basis multiplies every coordinate by the
same determinant. Thus diagonal recurrence applies to these coordinates
without an assumed projective-action interface.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped BigOperators ENNReal

namespace DukePrimeDegree

def frameMinor {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) : ℝ := (B.submatrix p id).det

lemma minor_diagonal_frame_mul {n k : ℕ}
    (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
    (R : Matrix (Fin k) (Fin k) ℝ) (p : Fin k ↪ Fin n) :
    frameMinor (Matrix.diagonal a * B * R) p =
      (∏ i, a (p i)) * frameMinor B p * R.det := by
  have he : (Matrix.diagonal a * B * R).submatrix p id =
      Matrix.diagonal (fun i => a (p i)) * B.submatrix p id * R := by
    ext i j
    change (∑ u, (Matrix.diagonal a * B) (p i) u * R u j) =
      ∑ u, (Matrix.diagonal (fun v => a (p v)) * B.submatrix p id) i u * R u j
    simp only [Matrix.diagonal_mul, Matrix.submatrix_apply, id_eq]
  change ((Matrix.diagonal a * B * R).submatrix p id).det = _
  rw [he, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  rfl

lemma measurable_frameMinor {Y : Type*} [MeasurableSpace Y] {n k : ℕ}
    (B : Y → Matrix (Fin n) (Fin k) ℝ)
    (hB : ∀ i j, Measurable (fun x => B x i j)) (p : Fin k ↪ Fin n) :
    Measurable (fun x => frameMinor (B x) p) := by
  have hm : Measurable (fun x => (B x).submatrix p id) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact hB (p i) j
  exact continuous_id.matrix_det.measurable.comp hm

/-- For a measurably transported real frame, two nonzero minors can
have only the same diagonal weight almost everywhere. This is the
projective recurrence conclusion in actual matrix coordinates. -/
theorem ae_frame_minors_have_one_diagonal_weight
    {Y : Type*} [MeasurableSpace Y] {n k : ℕ}
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (B : Y → Matrix (Fin n) (Fin k) ℝ)
    (hB : ∀ i j, Measurable (fun x => B x i j))
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (R : Y → Matrix (Fin k) (Fin k) ℝ)
    (hR : ∀ᵐ x ∂μ, (R x).det ≠ 0)
    (hcov : ∀ᵐ x ∂μ, B (T x) = Matrix.diagonal a * B x * R x) :
    ∀ᵐ x ∂μ, ∀ p q : Fin k ↪ Fin n,
      (∏ i, a (p i)) ≠ (∏ i, a (q i)) →
        frameMinor (B x) p = 0 ∨ frameMinor (B x) q = 0 := by
  apply ae_diagonal_projective_single_weight μ T hT
    (fun x p => frameMinor (B x) p) (measurable_frameMinor B hB)
    (fun p => ∏ i, a (p i)) (fun p => Finset.prod_pos (fun i _ => ha (p i)))
    (fun x => (R x).det) hR
  intro p
  filter_upwards [hcov] with x hx
  rw [hx, minor_diagonal_frame_mul]
  ring

end DukePrimeDegree

end

end OAI
