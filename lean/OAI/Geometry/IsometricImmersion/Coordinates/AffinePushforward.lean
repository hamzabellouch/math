import OAI.Geometry.IsometricImmersion.Coordinates.AffinePullback
import Mathlib.Topology.Algebra.Support

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def affineInverseCoordinates (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (p : Coord) : Coord := R⁻¹ *ᵥ (p - b)

theorem affineInverseCoordinates_contDiff (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiff ℝ ∞ (affineInverseCoordinates b R) :=
  (matrixContinuousLinear R⁻¹).contDiff.comp (contDiff_id.sub contDiff_const)

theorem affineInverseCoordinates_affineCoordinates (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) (q : Coord) :
    affineInverseCoordinates b R (affineCoordinates b R q) = q := by
  have hSR := Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  simp [affineInverseCoordinates, affineCoordinates, Matrix.mulVec_mulVec, hSR]

theorem affineCoordinates_affineInverseCoordinates (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) (p : Coord) :
    affineCoordinates b R (affineInverseCoordinates b R p) = p := by
  have hRS := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  simp [affineInverseCoordinates, affineCoordinates, Matrix.mulVec_mulVec, hRS]

def affineCoordinateHomeomorph (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : IsUnit R) : Coord ≃ₜ Coord where
  toFun := affineCoordinates b R
  invFun := affineInverseCoordinates b R
  left_inv := affineInverseCoordinates_affineCoordinates b R hR
  right_inv := affineCoordinates_affineInverseCoordinates b R hR
  continuous_toFun := (affineCoordinates_contDiff b R).continuous
  continuous_invFun := (affineInverseCoordinates_contDiff b R).continuous

def affinePushforwardMetric (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) : MetricField := fun p =>
  R⁻¹ᵀ * η (affineInverseCoordinates b R p) * R⁻¹

theorem affinePullback_pushforward (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    affinePullbackMetric (affinePushforwardMetric η b R) b R = η := by
  have hSR := Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  have hT : Rᵀ * R⁻¹ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hSR, Matrix.transpose_one]
  funext q
  simp only [affinePullbackMetric, affinePushforwardMetric,
    affineInverseCoordinates_affineCoordinates b R hR]
  calc
    _ = (Rᵀ * R⁻¹ᵀ) * η q * (R⁻¹ * R) := by simp only [Matrix.mul_assoc]
    _ = η q := by rw [hT, hSR, Matrix.one_mul, Matrix.mul_one]

theorem affinePushforward_pullback (g : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    affinePushforwardMetric (affinePullbackMetric g b R) b R = g := by
  have hRS := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  have hT : R⁻¹ᵀ * Rᵀ = 1 := by
    rw [← Matrix.transpose_mul, hRS, Matrix.transpose_one]
  funext p
  simp only [affinePullbackMetric, affinePushforwardMetric,
    affineCoordinates_affineInverseCoordinates b R hR]
  calc
    _ = (R⁻¹ᵀ * Rᵀ) * g p * (R * R⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g p := by rw [hT, hRS, Matrix.one_mul, Matrix.mul_one]

theorem affinePullbackMetric_add (g η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) :
    affinePullbackMetric (g + η) b R =
      affinePullbackMetric g b R + affinePullbackMetric η b R := by
  funext p
  simp only [affinePullbackMetric, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]

theorem affinePullback_add_pushforward (g η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    affinePullbackMetric (g + affinePushforwardMetric η b R) b R =
      affinePullbackMetric g b R + η := by
  rw [affinePullbackMetric_add, affinePullback_pushforward η b R hR]

theorem affinePushforwardMetric_eq_zero_iff (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) (p : Coord) :
    affinePushforwardMetric η b R p = 0 ↔ η (affineInverseCoordinates b R p) = 0 := by
  constructor
  · intro hp
    have h := congrFun (affinePullback_pushforward η b R hR)
      (affineInverseCoordinates b R p)
    simp only [affinePullbackMetric, affineCoordinates_affineInverseCoordinates b R hR,
      hp, Matrix.mul_zero, Matrix.zero_mul] at h
    exact h.symm
  · intro hp
    simp only [affinePushforwardMetric, hp, Matrix.mul_zero, Matrix.zero_mul]

theorem affinePushforwardMetric_support (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    Function.support (affinePushforwardMetric η b R) =
      affineCoordinates b R '' Function.support η := by
  ext p
  constructor
  · intro hp
    refine ⟨affineInverseCoordinates b R p, ?_,
      affineCoordinates_affineInverseCoordinates b R hR p⟩
    change η (affineInverseCoordinates b R p) ≠ 0
    intro hη
    exact hp ((affinePushforwardMetric_eq_zero_iff η b R hR p).mpr hη)
  · rintro ⟨q, hq, rfl⟩
    change affinePushforwardMetric η b R (affineCoordinates b R q) ≠ 0
    intro hη
    have hzero := (affinePushforwardMetric_eq_zero_iff η b R hR _).mp hη
    rw [affineInverseCoordinates_affineCoordinates b R hR] at hzero
    exact hq hzero

theorem affinePushforwardMetric_tsupport (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    tsupport (affinePushforwardMetric η b R) = affineCoordinates b R '' tsupport η := by
  rw [tsupport, affinePushforwardMetric_support η b R hR]
  exact ((affineCoordinateHomeomorph b R hR).image_closure (Function.support η)).symm

theorem affinePushforwardMetric_tsupport_subset (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) {P : Set Coord}
    (hP : tsupport η ⊆ P) :
    tsupport (affinePushforwardMetric η b R) ⊆ affineCoordinates b R '' P := by
  rw [affinePushforwardMetric_tsupport η b R hR]
  exact Set.image_mono hP

theorem affinePushforwardMetric_contDiff (η : MetricField)
    (hη : ∀ i j, ContDiff ℝ ∞ (fun p => η p i j))
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun p => affinePushforwardMetric η b R p i j) := by
  have hc (a k : Fin 2) : ContDiff ℝ ∞
      (fun p => η (affineInverseCoordinates b R p) a k) :=
    (hη a k).comp (affineInverseCoordinates_contDiff b R)
  simp only [affinePushforwardMetric, Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiff.sum
  intro k _
  apply ContDiff.mul _ contDiff_const
  apply ContDiff.sum
  intro a _
  exact contDiff_const.mul (hc a k)

end SmoothLocal.Geometry

end

end OAI
