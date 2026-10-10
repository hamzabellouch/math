import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedModes
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace OAI

/-! Volume-preserving planar/transverse coordinates for the actual
three-dimensional Coulomb space. The intermediate product has its Euclidean
L² norm; the final ordinary product carries the same product volume. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def verticalCoordinateEquiv : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ where
  __ := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toLinearEquiv
  norm_map' := by
    intro x
    change ‖x 0‖ = ‖x‖
    simp [PiLp.norm_eq_of_L2, Real.sqrt_sq_eq_abs]

def positionSplitIsometry : Position ≃ₗᵢ[ℝ] WithLp 2 SplitPosition :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((finSumFinEquiv (m := 2) (n := 1)).symm)).trans
    ((PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ => ℝ)).trans
      (LinearIsometryEquiv.withLpProdCongr 2
        (LinearIsometryEquiv.refl ℝ PlanarPosition) verticalCoordinateEquiv))

def positionSplitCoordinates : Position ≃L[ℝ] SplitPosition :=
  positionSplitIsometry.toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ PlanarPosition ℝ)

theorem positionSplitCoordinates_measurePreserving :
    MeasurePreserving positionSplitCoordinates := by
  change MeasurePreserving (fun x => WithLp.ofLp (positionSplitIsometry x))
  exact (WithLp.volume_preserving_ofLp PlanarPosition ℝ).comp
    positionSplitIsometry.measurePreserving

theorem positionSplitCoordinates_integral (f : SplitPosition → ℝ) :
    (∫ x : Position, f (positionSplitCoordinates x)) = ∫ p, f p :=
  positionSplitCoordinates_measurePreserving.integral_comp
    positionSplitCoordinates.toHomeomorph.measurableEmbedding f

theorem positionSplitCoordinates_norm_sq (x : Position) :
    ‖x‖ ^ 2 = ‖(positionSplitCoordinates x).1‖ ^ 2 +
      (positionSplitCoordinates x).2 ^ 2 := by
  change ‖x‖ ^ 2 = ‖(positionSplitIsometry x).fst‖ ^ 2 + (positionSplitIsometry x).snd ^ 2
  have h := WithLp.prod_norm_sq_eq_of_L2 (positionSplitIsometry x)
  rw [positionSplitIsometry.norm_map] at h
  simpa only [Real.norm_eq_abs, sq_abs] using h

theorem positionSplitCoordinates_distance (x y : Position) :
    ‖x - y‖ = Real.sqrt (‖(positionSplitCoordinates x).1 - (positionSplitCoordinates y).1‖ ^ 2 +
      ((positionSplitCoordinates x).2 - (positionSplitCoordinates y).2) ^ 2) := by
  have h := positionSplitCoordinates_norm_sq (x - y)
  rw [map_sub] at h
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

def continuumLocalizedMode (freq : ℝ) (u : PlanarPosition) (x : Position) : ℝ :=
  localizedMode freq u (positionSplitCoordinates x)

theorem continuumLocalizedMode_C7 (freq : ℝ) (u : PlanarPosition) :
    ContDiff ℝ 7 (continuumLocalizedMode freq u) :=
  (localizedMode_C7 freq u).comp positionSplitCoordinates.contDiff

theorem continuumLocalizedMode_positive {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) : 0 < continuumLocalizedMode freq u x :=
  localizedMode_positive hfreq u _

theorem continuumLocalizedMode_normalized {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : (∫ x : Position, continuumLocalizedMode freq u x ^ 2) = 1 := by
  change (∫ x : Position, (localizedMode freq u (positionSplitCoordinates x)) ^ 2) = 1
  rw [positionSplitCoordinates_integral (fun p => localizedMode freq u p ^ 2),
    localizedMode_normalized hfreq]

theorem continuumLocalizedMode_memLp {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    MemLp (continuumLocalizedMode freq u) 2 :=
  (localizedMode_memLp hfreq u).comp_measurePreserving positionSplitCoordinates_measurePreserving

end ContinuumCoulomb

end

end OAI
