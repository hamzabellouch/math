import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFiniteRankResolvent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Normed.Algebra.Spectrum

namespace OAI

/-! # Invertibility reduces to the actual finite-dimensional remainder

This is the finite-dimensional Schur complement of the checked resolvent
formula. It will be applied to a contraction plus the actual finite-rank
remainder of the linearized time step.
-/

namespace DefocusingNLS

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

local instance : CompleteSpace F := FiniteDimensional.complete ℂ F

theorem finiteRank_isUnit_iff (A : E →L[ℂ] E) (U : F →L[ℂ] E)
    (V : E →L[ℂ] F) (hA : IsUnit A) :
    IsUnit (A - U.comp V) ↔
      IsUnit (ContinuousLinearMap.id ℂ F - V.comp ((Ring.inverse A).comp U)) := by
  let R := Ring.inverse A
  let D := ContinuousLinearMap.id ℂ F - V.comp (R.comp U)
  have hAR : A.comp R = ContinuousLinearMap.id ℂ E := Ring.mul_inverse_cancel A hA
  have hRA : R.comp A = ContinuousLinearMap.id ℂ E := Ring.inverse_mul_cancel A hA
  have hARx (x : E) : A (R x) = x :=
    congrArg (fun L : E →L[ℂ] E => L x) hAR
  constructor
  · intro hS
    have hSinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hS).1
    have hDinj : Function.Injective D := by
      intro x y hxy
      have hz : D (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      change x - y - V (R (U (x - y))) = 0 at hz
      have hw : x - y = V (R (U (x - y))) := sub_eq_zero.mp hz
      have hU := congrArg U hw
      have hs : (A - U.comp V) (R (U (x - y))) = 0 := by
        change A (R (U (x - y))) - U (V (R (U (x - y)))) = 0
        rw [hARx]
        exact sub_eq_zero.mpr hU
      have hr : R (U (x - y)) = 0 := hSinj (hs.trans (map_zero _).symm)
      have hw0 : x - y = 0 := hw.trans (by rw [hr, map_zero])
      exact sub_eq_zero.mp hw0
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hDinj, LinearMap.injective_iff_surjective.mp hDinj⟩
  · intro hD
    let W := Ring.inverse D
    have hDW : D.comp W = ContinuousLinearMap.id ℂ F := Ring.mul_inverse_cancel D hD
    have hWD : W.comp D = ContinuousLinearMap.id ℂ F := Ring.inverse_mul_cancel D hD
    have hleft := finiteRankResolvent_left A R U V W hAR hDW
    have hright := finiteRankResolvent_right A R U V W hRA hWD
    exact ⟨⟨A - U.comp V, finiteRankResolvent R U V W, hleft, hright⟩, rfl⟩

/-- The only obstruction is the determinant on the finite-dimensional range. -/
theorem finiteRank_isUnit_iff_det_ne_zero (A : E →L[ℂ] E) (U : F →L[ℂ] E)
    (V : E →L[ℂ] F) (hA : IsUnit A) :
    IsUnit (A - U.comp V) ↔
      (ContinuousLinearMap.id ℂ F - V.comp ((Ring.inverse A).comp U)).det ≠ 0 := by
  rw [finiteRank_isUnit_iff A U V hA, ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap,
    LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- Outside the spectrum of the contracting part, the spectral problem is finite-dimensional. -/
theorem finiteRank_spectrum_iff_det_zero (B : E →L[ℂ] E) (U : F →L[ℂ] E)
    (V : E →L[ℂ] F) (z : ℂ) (hz : z ∈ resolventSet ℂ B) :
    z ∈ spectrum ℂ (B + U.comp V) ↔
      (ContinuousLinearMap.id ℂ F - V.comp ((resolvent B z).comp U)).det = 0 := by
  have he : algebraMap ℂ (E →L[ℂ] E) z - (B + U.comp V) =
      (algebraMap ℂ (E →L[ℂ] E) z - B) - U.comp V := by abel
  rw [spectrum.mem_iff, he]
  have h := finiteRank_isUnit_iff_det_ne_zero
    (algebraMap ℂ (E →L[ℂ] E) z - B) U V hz
  simpa only [resolvent, not_not] using not_congr h

end

end DefocusingNLS

end OAI
