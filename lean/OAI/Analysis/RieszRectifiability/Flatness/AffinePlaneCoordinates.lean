import Mathlib

namespace OAI

/-!
# Affine plane coordinates

A linear isometric embedding determines an affine plane parametrization and an
adjoint coordinate map. These maps are Lipschitz and recover every parameter on
the plane; their composition also gives a Lipschitz distance-to-plane function.
-/

namespace RieszRectifiability

noncomputable section

open Function WithLp
open scoped NNReal ENNReal

def affinePlaneSection {n d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (u : Fin n → ℝ) : EuclideanSpace ℝ (Fin d) := a + L (toLp 2 u)

def affinePlaneCoordinates {n d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : Fin n → ℝ :=
  ofLp (L.toContinuousLinearMap.adjoint (x - a))

theorem affinePlaneSection_lipschitz {n d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    LipschitzWith ((Fintype.card (Fin n) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal)
      (affinePlaneSection a L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [affinePlaneSection, dist_add_left, L.dist_map]
  exact (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).dist_le_mul x y

theorem affinePlaneCoordinates_lipschitz {n d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    LipschitzWith ‖L.toContinuousLinearMap.adjoint‖₊ (affinePlaneCoordinates a L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℝ)).dist_le_mul
    (L.toContinuousLinearMap.adjoint (x - a)) (L.toContinuousLinearMap.adjoint (y - a))
  simp only [NNReal.coe_one, one_mul] at h
  exact h.trans (by simpa only [dist_sub_right] using!
    L.toContinuousLinearMap.adjoint.lipschitzWith.dist_le_mul (x - a) (y - a))

theorem affinePlaneCoordinates_leftInverse {n d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    LeftInverse (affinePlaneCoordinates a L) (affinePlaneSection a L) := by
  intro u
  have h : L.toContinuousLinearMap.adjoint (L (toLp 2 u)) = toLp 2 u := by
    exact DFunLike.congr_fun L.adjoint_comp_self (toLp 2 u)
  change ofLp (L.toContinuousLinearMap.adjoint ((a + L (toLp 2 u)) - a)) = u
  rw [add_sub_cancel_left, h]

theorem affinePlaneHeight_lipschitz {n d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∃ K : ℝ≥0, LipschitzWith K
      (fun x => dist x (affinePlaneSection a L (affinePlaneCoordinates a L x))) := by
  have h := (affinePlaneSection_lipschitz a L).comp (affinePlaneCoordinates_lipschitz a L)
  exact ⟨_, LipschitzWith.dist.comp (LipschitzWith.id.prodMk h)⟩

end

end RieszRectifiability

end OAI
