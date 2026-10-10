import OAI.Probability.InvariantIsing.Cavity.CavityProjectorStabilizer
import OAI.Probability.InvariantIsing.Cavity.CavityProjectedSpinNumerator

namespace OAI

/-! Selected columns in spectral groups and their exact spin coordinates.
These are the vectors to which the fresh-frame Gaussian limit applies. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityGroupedSelectedFrame {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ) : Matrix (Fin N) (Fin d) ℝ :=
  fun i j => (cavityGroupFrame k e (f j).1 * A (f j).1) i (f j).2

def cavityGroupSpinCoordinates {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (V : Orthogonal N)
    (a : Fin m) (σ : Spin N) : Fin (k a) → ℝ :=
  fun j => ((V : Matrix (Fin N) (Fin N) ℝ).transpose *ᵥ
    (fun i => spinValue (σ i))) (e ⟨a,j⟩)

lemma cavityGroupedSelectedFrame_rotation {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (W : (a : Fin m) → Orthogonal (k a)) :
    (cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*
      cavityGroupedSelectedFrame k e f A =
    cavityGroupedSelectedFrame k e f (cavityGroupHaarFrames A W) := by
  ext i j
  change ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*
    (cavityGroupFrame k e (f j).1*A (f j).1)) i (f j).2 = _
  rw [← Matrix.mul_assoc, cavityGroupRotation_frame, Matrix.mul_assoc]
  rfl

lemma cavityGroupFrame_transpose_mulVec {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m)
    (x : Fin N → ℝ) (j : Fin (k a)) :
    ((cavityGroupFrame k e a).transpose *ᵥ x) j = x (e ⟨a,j⟩) := by
  simp [Matrix.mulVec, dotProduct, cavityGroupFrame]

lemma cavityGroupedSelectedFrame_transpose_mulVec {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ) (x : Fin N → ℝ)
    (j : Fin d) :
    ((cavityGroupedSelectedFrame k e f A).transpose *ᵥ x) j =
      ∑ l, x (e ⟨(f j).1,l⟩)*A (f j).1 l (f j).2 := by
  change (((cavityGroupFrame k e (f j).1*A (f j).1).transpose) *ᵥ x) (f j).2 = _
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
  change (∑ l, A (f j).1 l (f j).2 *
    ((cavityGroupFrame k e (f j).1).transpose *ᵥ x) l) = _
  simp only [cavityGroupFrame_transpose_mulVec]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma cavityGroupedSelectedFrame_coordinates {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (V : Orthogonal N) (σ : Spin N) :
    cavityFrameCoordinates ((V : Matrix (Fin N) (Fin N) ℝ)*
      cavityGroupedSelectedFrame k e f A) σ =
    cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V) A σ := by
  ext j
  change (((V : Matrix (Fin N) (Fin N) ℝ)*
    cavityGroupedSelectedFrame k e f A).transpose *ᵥ (fun i => spinValue (σ i))) j = _
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec,
    cavityGroupedSelectedFrame_transpose_mulVec]
  rfl

lemma cavityGroupedSelectedFrame_rotated_coordinates {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (V : Orthogonal N) (W : (a : Fin m) → Orthogonal (k a)) (σ : Spin N) :
    cavityFrameCoordinates ((V : Matrix (Fin N) (Fin N) ℝ)*
      ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*
        cavityGroupedSelectedFrame k e f A)) σ =
    cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
      (cavityGroupHaarFrames A W) σ := by
  rw [cavityGroupedSelectedFrame_rotation, cavityGroupedSelectedFrame_coordinates]

end InvariantIsing

end

end OAI
