import OAI.Geometry.RCD.Coordinates.CoordinateBilinear
import OAI.Geometry.RCD.Metric.LocalSignedMeasureOrder

namespace OAI

/-! # Linear integration of the finite signed coefficient measures -/

open Set MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

def signedTestIntegral (w : X →ᵇ ℝ) : SignedMeasure X →ₗ[ℝ] ℝ where
  toFun ν := ∫ᵛ x, w x ∂<•ν
  map_add' μ ν := VectorMeasure.integral_add_vectorMeasure
    (PositiveBilinearMeasure.integrable_weight w μ) (PositiveBilinearMeasure.integrable_weight w ν)
  map_smul' a ν := by simp only [VectorMeasure.integral_smul_vectorMeasure, smul_eq_mul, RingHom.id_apply]

theorem signedTestIntegral_restrict (w : X →ᵇ ℝ) (ν : SignedMeasure X)
    {S : Set X} (hS : MeasurableSet S) (hw : tsupport w ⊆ S) :
    signedTestIntegral w (ν.restrict S) = signedTestIntegral w ν := by
  apply VectorMeasure.setIntegral_eq_integral_of_forall_compl_eq_zero hS
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (fun hs => hx (hw hs))

theorem signedTestIntegral_coordinate {m : ℕ} (w : X →ᵇ ℝ)
    (a : Fin m → Fin m → SignedMeasure X) (v z : Euclidean m) :
    signedTestIntegral w (coordinateBilinear a v z) =
      ∑ i : Fin m, ∑ j : Fin m, (v i * z j) * signedTestIntegral w (a i j) := by
  rw [coordinateBilinear_apply]
  simp only [map_sum, map_smul, smul_eq_mul]

end RegularPointCoordinates

end

end OAI
