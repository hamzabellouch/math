import OAI.Geometry.EinsteinFour.OrthonormalFrame
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace OAI

/-! The cotangent-coordinate calculation used by the geodesic measure
argument: a Hamiltonian vector field has zero coordinate divergence.
Only the four-dimensional position and momentum coordinates needed here
are introduced. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

abbrev CotangentCoordinates := FourSpace × FourSpace

def positionDirection (r : Fin 4) : CotangentCoordinates := (coordinateVector r, 0)
def momentumDirection (r : Fin 4) : CotangentCoordinates := (0, coordinateVector r)

def cotangentHamiltonianField (H : CotangentCoordinates → ℝ)
    (z : CotangentCoordinates) : CotangentCoordinates :=
  (WithLp.toLp 2 (fun r => fderiv ℝ H z (momentumDirection r)),
    WithLp.toLp 2 (fun r => -fderiv ℝ H z (positionDirection r)))

/-- Coordinate divergence in the position and momentum basis. -/
def cotangentDivergence (X : CotangentCoordinates → CotangentCoordinates)
    (z : CotangentCoordinates) : ℝ :=
  ∑ r, (fderiv ℝ (fun w => (X w).1 r) z (positionDirection r) +
    fderiv ℝ (fun w => (X w).2 r) z (momentumDirection r))

theorem cotangentHamiltonian_energy_rate (H : CotangentCoordinates → ℝ)
    (z : CotangentCoordinates) :
    fderiv ℝ H z (cotangentHamiltonianField H z) = 0 := by
  let L := fderiv ℝ H z
  let v : FourSpace := WithLp.toLp 2 (fun r => L (momentumDirection r))
  let w : FourSpace := WithLp.toLp 2 (fun r => -L (positionDirection r))
  have hv : (v, 0) = ∑ r, L (momentumDirection r) • positionDirection r := by
    simpa only [map_sum, map_smul, LinearMap.inl_apply, positionDirection, v] using
      (congrArg (LinearMap.inl ℝ FourSpace FourSpace)
        (sum_coordinateVector (fun r => L (momentumDirection r)))).symm
  have hw : (0, w) = ∑ r, (-L (positionDirection r)) • momentumDirection r := by
    simpa only [map_sum, map_smul, LinearMap.inr_apply, momentumDirection, w] using
      (congrArg (LinearMap.inr ℝ FourSpace FourSpace)
        (sum_coordinateVector (fun r => -L (positionDirection r)))).symm
  change L (v, w) = 0
  rw [show (v, w) = (v, 0) + (0, w) by simp, map_add, hv, hw, map_sum, map_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro r _
  simp only [map_smul, smul_eq_mul]
  ring

/-- A solution of Hamilton's equations has zero energy derivative. -/
theorem hasDerivAt_cotangentHamiltonian_energy
    (H : CotangentCoordinates → ℝ) (γ : ℝ → CotangentCoordinates) (t : ℝ)
    (hH : DifferentiableAt ℝ H (γ t))
    (hγ : HasDerivAt γ (cotangentHamiltonianField H (γ t)) t) :
    HasDerivAt (fun s => H (γ s)) 0 t := by
  have h := hH.hasFDerivAt.comp_hasDerivAt t hγ
  rwa [cotangentHamiltonian_energy_rate] at h

theorem cotangentHamiltonian_energy_constant
    (H : CotangentCoordinates → ℝ) (γ : ℝ → CotangentCoordinates)
    (hH : ∀ t, DifferentiableAt ℝ H (γ t))
    (hγ : ∀ t, HasDerivAt γ (cotangentHamiltonianField H (γ t)) t)
    (s t : ℝ) : H (γ s) = H (γ t) := by
  have hd (r : ℝ) := hasDerivAt_cotangentHamiltonian_energy H γ r (hH r) (hγ r)
  exact isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    (fun r _ => (hd r).differentiableAt.differentiableWithinAt)
    (fun r _ => (hd r).deriv) (Set.mem_univ s) (Set.mem_univ t)

private theorem hamiltonian_partial_derivative
    (H : CotangentCoordinates → ℝ) (z u v : CotangentCoordinates)
    (hH : ContDiffAt ℝ ∞ H z) :
    fderiv ℝ (fun w => fderiv ℝ H w u) z v =
      fderiv ℝ (fderiv ℝ H) z v u := by
  have hd := ((hH.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have h := congrArg (fun L : CotangentCoordinates →L[ℝ] ℝ => L v)
    (hd.clm_apply (hasFDerivAt_const u z)).fderiv
  simpa using h

/-- The two mixed derivatives cancel in each position--momentum pair.
This proves the local divergence statement; flow Jacobians and restriction
to the unit-energy shell are separate geometric steps. -/
theorem cotangentHamiltonian_divergence_zero
    (H : CotangentCoordinates → ℝ) (z : CotangentCoordinates)
    (hH : ContDiffAt ℝ ∞ H z) :
    cotangentDivergence (cotangentHamiltonianField H) z = 0 := by
  unfold cotangentDivergence
  apply Finset.sum_eq_zero
  intro r _
  change fderiv ℝ (fun w => fderiv ℝ H w (momentumDirection r)) z
      (positionDirection r) +
    fderiv ℝ (fun w => -fderiv ℝ H w (positionDirection r)) z
      (momentumDirection r) = 0
  rw [fderiv_fun_neg, neg_apply,
    hamiltonian_partial_derivative H z (momentumDirection r) (positionDirection r) hH,
    hamiltonian_partial_derivative H z (positionDirection r) (momentumDirection r) hH]
  have hs := hH.isSymmSndFDerivAt (by simp) (positionDirection r) (momentumDirection r)
  rw [hs]
  exact add_neg_cancel _

end
end PositiveEinsteinFour.Geometry

end OAI
