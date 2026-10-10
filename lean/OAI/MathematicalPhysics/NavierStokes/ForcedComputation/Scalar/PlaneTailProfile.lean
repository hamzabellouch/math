import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneBarrier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.Deriv.ZPow

namespace OAI

/-! An integrable rational profile on the whole plane with derivative bounds
controlling diffusion tails. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set MeasureTheory
open scoped ContDiff

def planeTailProfile (x : Plane) : ℝ := (planeBarrierSquare x)⁻¹ ^ 2

theorem planeBarrierSquare_pos (x : Plane) : 0 < planeBarrierSquare x :=
  lt_of_lt_of_le (by norm_num) (planeBarrierSquare_one_le x)

theorem planeTailProfile_pos (x : Plane) : 0 < planeTailProfile x := by
  exact pow_pos (inv_pos.mpr (planeBarrierSquare_pos x)) 2

theorem planeTailProfile_smooth : ContDiff ℝ ∞ planeTailProfile :=
  (planeBarrierSquare_smooth.inv (fun x => (planeBarrierSquare_pos x).ne')).pow 2

theorem planeTailProfile_le_one (x : Plane) : planeTailProfile x ≤ 1 := by
  have hi : (planeBarrierSquare x)⁻¹ ≤ 1 :=
    (inv_le_one₀ (planeBarrierSquare_pos x)).mpr (planeBarrierSquare_one_le x)
  have hn : 0 ≤ (planeBarrierSquare x)⁻¹ := (inv_pos.mpr (planeBarrierSquare_pos x)).le
  change (planeBarrierSquare x)⁻¹ ^ 2 ≤ 1
  nlinarith

theorem planeTailProfile_fderiv (x v : Plane) :
    fderiv ℝ planeTailProfile x v =
      -4 * (x 0 * v 0 + x 1 * v 1) * (planeBarrierSquare x)⁻¹ ^ 3 := by
  have hz := (planeBarrierSquare_pos x).ne'
  have hd := (hasDerivAt_zpow (-2) (planeBarrierSquare x) (Or.inl hz)).comp_hasFDerivAt x
    (planeBarrierSquare_smooth.differentiable (by simp) x).hasFDerivAt
  have he : (fun y : Plane => planeBarrierSquare y ^ (-2 : ℤ)) = planeTailProfile := by
    funext y
    simp [planeTailProfile, zpow_neg]
  change HasFDerivAt (fun y => planeBarrierSquare y ^ (-2 : ℤ)) _ x at hd
  rw [he] at hd
  rw [hd.fderiv]
  simp [planeBarrierSquare_fderiv, zpow_neg]
  ring

theorem planeTailProfile_spatialD (j : Fin 2) :
    spatialD j planeTailProfile = fun x => -4 * x j * (planeBarrierSquare x)⁻¹ ^ 3 := by
  funext x
  rw [spatialD, planeTailProfile_fderiv]
  fin_cases j <;> simp [PlanarHamiltonian.basis]

theorem planeTailProfile_secondD (j : Fin 2) (x : Plane) :
    spatialD j (spatialD j planeTailProfile) x =
      -4 * (planeBarrierSquare x)⁻¹ ^ 3 +
        24 * (x j) ^ 2 * (planeBarrierSquare x)⁻¹ ^ 4 := by
  have hz := (planeBarrierSquare_pos x).ne'
  have hd := (hasDerivAt_zpow (-3) (planeBarrierSquare x) (Or.inl hz)).comp_hasFDerivAt x
    (planeBarrierSquare_smooth.differentiable (by simp) x).hasFDerivAt
  have he : (fun y : Plane => planeBarrierSquare y ^ (-3 : ℤ)) =
      (fun y => (planeBarrierSquare y)⁻¹ ^ 3) := by
    funext y
    simp [zpow_neg]
  change HasFDerivAt (fun y => planeBarrierSquare y ^ (-3 : ℤ)) _ x at hd
  rw [he] at hd
  have hh := ((hasFDerivAt_apply (𝕜 := ℝ) j x).const_mul (-4)).mul hd
  rw [planeTailProfile_spatialD]
  change fderiv ℝ (fun y : Plane => -4 * y j * (planeBarrierSquare y)⁻¹ ^ 3) x
    (PlanarHamiltonian.basis j) = _
  change HasFDerivAt (fun y : Plane => -4 * y j * (planeBarrierSquare y)⁻¹ ^ 3) _ x at hh
  rw [hh.fderiv]
  fin_cases j <;> simp [planeBarrierSquare_fderiv, PlanarHamiltonian.basis, zpow_neg] <;> ring

theorem planeTailProfile_laplacian (x : Plane) :
    scalarLaplacian planeTailProfile x =
      -8 * (planeBarrierSquare x)⁻¹ ^ 3 +
        24 * ((x 0) ^ 2 + (x 1) ^ 2) * (planeBarrierSquare x)⁻¹ ^ 4 := by
  simp [scalarLaplacian, planeTailProfile_secondD, Fin.sum_univ_two]
  ring

theorem planeBarrierSquare_norm_sq (x : Plane) :
    1 + ‖x‖ ^ 2 ≤ planeBarrierSquare x := by
  have hc (j : Fin 2) : |x j| ≤ Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) := by
    apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
    fin_cases j
    · change |x 0| ^ 2 ≤ (x 0) ^ 2 + (x 1) ^ 2
      rw [sq_abs]
      nlinarith [sq_nonneg (x 1)]
    · change |x 1| ^ 2 ≤ (x 0) ^ 2 + (x 1) ^ 2
      rw [sq_abs]
      nlinarith [sq_nonneg (x 0)]
  have hn : ‖x‖ ≤ Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    exact hc j
  have hs := Real.sq_sqrt (show 0 ≤ (x 0) ^ 2 + (x 1) ^ 2 by positivity)
  unfold planeBarrierSquare
  nlinarith [norm_nonneg x]

theorem planeTailProfile_integrable : Integrable planeTailProfile := by
  have hi : Integrable (fun x : Plane => (1 + ‖x‖ ^ 2)⁻¹ ^ 2) := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := Plane) (μ := volume)
      (r := 4) (by norm_num)
    convert h using 1
    funext x
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  apply hi.mono' planeTailProfile_smooth.continuous.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (planeTailProfile_pos x)]
  have hp : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have he := (inv_le_inv₀ (planeBarrierSquare_pos x) hp).mpr
    (planeBarrierSquare_norm_sq x)
  exact pow_le_pow_left₀ (inv_pos.mpr (planeBarrierSquare_pos x)).le he 2

end ForcedComputation.VelocityDetector

end

end OAI
