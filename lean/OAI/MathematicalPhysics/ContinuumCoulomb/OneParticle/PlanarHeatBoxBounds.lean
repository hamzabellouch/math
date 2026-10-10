import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatBoxCoordinates
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.HeatDensityModulus

namespace OAI

/-! Explicit coordinate bounds on the fixed forcing square. They turn
the kernel estimates into concrete quadrature constants for every input
point, with polynomial dependence on its magnitude. -/

noncomputable section
namespace ContinuumCoulomb

theorem planarPair_norm_sq (p : ℝ × ℝ) :
    ‖planarPairEquiv.symm p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, planarPairEquiv_symm_apply]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]

theorem planarPair_norm_le_two {p : ℝ × ℝ}
    (hp : p ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) :
    ‖planarPairEquiv.symm p‖ ≤ 2 := by
  have h1 : p.1 ^ 2 ≤ 1 := by
    have hz := mul_nonneg (sub_nonneg.mpr hp.1.2) (show 0 ≤ 1 + p.1 by linarith [hp.1.1])
    nlinarith
  have h2 : p.2 ^ 2 ≤ 1 := by
    have hz := mul_nonneg (sub_nonneg.mpr hp.2.2) (show 0 ≤ 1 + p.2 by linarith [hp.2.1])
    nlinarith
  have hn := planarPair_norm_sq p
  nlinarith [norm_nonneg (planarPairEquiv.symm p)]

theorem planarPair_distance_first (x x' y : ℝ) :
    ‖planarPairEquiv.symm (x, y) - planarPairEquiv.symm (x', y)‖ = |x - x'| := by
  have heq : planarPairEquiv.symm (x, y) - planarPairEquiv.symm (x', y) =
      planarPairEquiv.symm (x - x', 0) := by
    rw [planarPairEquiv_symm_apply, planarPairEquiv_symm_apply, planarPairEquiv_symm_apply]
    ext i
    fin_cases i <;> simp
  rw [heq]
  have h := planarPair_norm_sq (x - x', 0)
  nlinarith [norm_nonneg (planarPairEquiv.symm (x - x', 0)), abs_nonneg (x - x'), sq_abs (x - x')]

theorem planarPair_distance_second (x y y' : ℝ) :
    ‖planarPairEquiv.symm (x, y) - planarPairEquiv.symm (x, y')‖ = |y - y'| := by
  have heq : planarPairEquiv.symm (x, y) - planarPairEquiv.symm (x, y') =
      planarPairEquiv.symm (0, y - y') := by
    rw [planarPairEquiv_symm_apply, planarPairEquiv_symm_apply, planarPairEquiv_symm_apply]
    ext i
    fin_cases i <;> simp
  rw [heq]
  have h := planarPair_norm_sq (0, y - y')
  nlinarith [norm_nonneg (planarPairEquiv.symm (0, y - y')), abs_nonneg (y - y'), sq_abs (y - y')]

theorem planarPair_distance_bound (r : PlanarPosition) {p : ℝ × ℝ}
    (hp : p ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) :
    ‖r - planarPairEquiv.symm p‖ ≤ ‖r‖ + 2 :=
  (norm_sub_le _ _).trans (add_le_add_right (planarPair_norm_le_two hp) _)

def planarBoxSpatialConstant (r : PlanarPosition) (η : ℝ) : ℝ :=
  2 * (‖r‖ + 2) / η ^ 2 + 32 * η⁻¹

def planarBoxTimeConstant (r : PlanarPosition) (η : ℝ) : ℝ :=
  η⁻¹ ^ 2 + η⁻¹ * (1 + (‖r‖ + 2) ^ 2 / (4 * η ^ 2))

theorem planarBox_spatial_first (r : PlanarPosition) {η t x x' y : ℝ}
    (hη : 0 < η) (ht : η ≤ t)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hx' : x' ∈ Set.Icc (-1 : ℝ) 1)
    (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    |HeatKernelModulus.density r t (planarPairEquiv.symm (x, y)) -
      HeatKernelModulus.density r t (planarPairEquiv.symm (x', y))| ≤
      planarBoxSpatialConstant r η * |x - x'| := by
  simpa only [planarPair_distance_first, planarBoxSpatialConstant] using
    HeatKernelModulus.density_space_lipschitz hη ht
      (planarPair_distance_bound r (p := (x, y)) ⟨hx, hy⟩)
      (planarPair_distance_bound r (p := (x', y)) ⟨hx', hy⟩)

theorem planarBox_spatial_second (r : PlanarPosition) {η t x y y' : ℝ}
    (hη : 0 < η) (ht : η ≤ t)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1)
    (hy' : y' ∈ Set.Icc (-1 : ℝ) 1) :
    |HeatKernelModulus.density r t (planarPairEquiv.symm (x, y)) -
      HeatKernelModulus.density r t (planarPairEquiv.symm (x, y'))| ≤
      planarBoxSpatialConstant r η * |y - y'| := by
  simpa only [planarPair_distance_second, planarBoxSpatialConstant] using
    HeatKernelModulus.density_space_lipschitz hη ht
      (planarPair_distance_bound r (p := (x, y)) ⟨hx, hy⟩)
      (planarPair_distance_bound r (p := (x, y')) ⟨hx, hy'⟩)

theorem planarBox_time (r : PlanarPosition) {η t s x y : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hs : η ≤ s)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    |HeatKernelModulus.density r t (planarPairEquiv.symm (x, y)) -
      HeatKernelModulus.density r s (planarPairEquiv.symm (x, y))| ≤
      planarBoxTimeConstant r η * |t - s| :=
  HeatKernelModulus.density_time_lipschitz hη ht hs
    (planarPair_distance_bound r (p := (x, y)) ⟨hx, hy⟩)

end ContinuumCoulomb

end

end OAI
