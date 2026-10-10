import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedColumnBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

/-!+# Exact Euclidean volume of the weighted boxes

The determinant separates into the unscaled basis determinant and the
exponential of its total weight. This gives the exact exponential volume
rate of the coordinate box, before passage to nilpotent exponential charts.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace PolycyclicRecognition

variable {I : Type*} {n : ℕ}

def scaledColumnMatrix (v : I → Fin n → ℝ) (w : I → ℝ)
    (b : Fin n → I) (r : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.exp (r * w (b j)) * v (b j) i

theorem det_scaledColumnMatrix (v : I → Fin n → ℝ) (w : I → ℝ)
    (b : Fin n → I) (r : ℝ) :
    (scaledColumnMatrix v w b r).det =
      Real.exp (r * columnBasisWeight w b) * (columnBasisMatrix v b).det := by
  change (Matrix.of fun i j => Real.exp (r * w (b j)) * columnBasisMatrix v b i j).det = _
  rw [Matrix.det_mul_row, ← Real.exp_sum]
  congr 2
  exact (Finset.mul_sum _ _ _).symm

/-- The coordinate weighted box is an actual linear image of a cube. -/
def weightedCoordinateBox (v : I → Fin n → ℝ) (w : I → ℝ)
    (b : Fin n → I) (r L : ℝ) : Set (Fin n → ℝ) :=
  (Matrix.toLin' (scaledColumnMatrix v w b r)) ''
    Set.Icc (fun _ => -L) (fun _ => L)

theorem isCompact_weightedCoordinateBox (v : I → Fin n → ℝ) (w : I → ℝ)
    (b : Fin n → I) (r L : ℝ) : IsCompact (weightedCoordinateBox v w b r L) :=
  isCompact_Icc.image (LinearMap.continuous_of_finiteDimensional _)

/-- The exact coordinate-volume formula; in particular, the exponent is
the total weight of the selected basis. -/
theorem volume_weightedCoordinateBox (v : I → Fin n → ℝ) (w : I → ℝ)
    (b : Fin n → I) (r L : ℝ) :
    volume (weightedCoordinateBox v w b r L) =
      ENNReal.ofReal |(columnBasisMatrix v b).det| *
        ENNReal.ofReal (Real.exp (r * columnBasisWeight w b)) *
          ENNReal.ofReal (2 * L) ^ n := by
  rw [weightedCoordinateBox, Measure.addHaar_image_linearMap,
    LinearMap.det_toLin', det_scaledColumnMatrix, abs_mul,
    abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)),
    Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ac_rfl

end PolycyclicRecognition

end

end OAI
