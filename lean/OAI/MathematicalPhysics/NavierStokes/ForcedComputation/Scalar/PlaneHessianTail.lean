import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneDerivativeTail
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace OAI

/-! Polarization turns the directional tail estimate into bounds for
every coordinate entry of the Hessian. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian MeasureTheory
open scoped ContDiff

theorem plane_basis_norm_le (j : Fin 2) : ‖basis j‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  simp only [PlanarHamiltonian.basis, Pi.single_apply, Real.norm_eq_abs]
  split_ifs <;> norm_num

theorem scalar_second_spatial_eq {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (j k : Fin 2) :
    spatialD j (spatialD k f) x = fderiv ℝ (fderiv ℝ f) x (basis j) (basis k) := by
  unfold spatialD
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const _)]
  simp

theorem scalar_hessian_entry_tail {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hfB : ∀ y, |f y| ≤ B * planeTailProfile y)
    (hfM : ∀ y, ‖iteratedFDeriv ℝ 3 f y‖ ≤ M)
    (x : Plane) (j k : Fin 2) :
    |spatialD j (spatialD k f) x| ≤ 3 * (100 * B + M) * derivativeTail x := by
  let H := fderiv ℝ (fderiv ℝ f) x
  let C := (100 * B + M) * derivativeTail x
  have hC : 0 ≤ C := mul_nonneg (by positivity) (derivativeTail_pos x).le
  have hs (u v : Plane) : H u v = H v u :=
    hf.contDiffAt.isSymmSndFDerivAt (by simp) u v
  have hdiag (v : Plane) (hv : ‖v‖ ≤ 1) : |H v v| ≤ C := by
    simpa only [iteratedFDeriv_two_apply, H, C] using
      scalar_second_directional_tail hf hB hM hfB hfM x v hv
  let u := basis j
  let v := basis k
  let z := (1 / 2 : ℝ) • (u + v)
  have hu : ‖u‖ ≤ 1 := plane_basis_norm_le j
  have hv : ‖v‖ ≤ 1 := plane_basis_norm_le k
  have hz : ‖z‖ ≤ 1 := by
    have ha := norm_add_le u v
    dsimp [z]
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  have hp : 4 * H z z = H u u + 2 * H u v + H v v := by
    dsimp [z]
    simp only [map_smul, smul_apply, smul_eq_mul,
      map_add, add_apply, hs v u]
    ring
  have h0 := abs_le.mp (hdiag u hu)
  have h1 := abs_le.mp (hdiag v hv)
  have h2 := abs_le.mp (hdiag z hz)
  rw [scalar_second_spatial_eq hf]
  change |H u v| ≤ 3 * (100 * B + M) * derivativeTail x
  have hb : |H u v| ≤ 3 * C := by
    apply abs_le.mpr
    constructor <;> linarith
  simpa only [C, mul_assoc] using hb


theorem scalar_hessian_square_integrable {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hfB : ∀ y, |f y| ≤ B * planeTailProfile y)
    (hfM : ∀ y, ‖iteratedFDeriv ℝ 3 f y‖ ≤ M) (j k : Fin 2) :
    Integrable (fun x => (spatialD j (spatialD k f) x) ^ 2) := by
  let A := 3 * (100 * B + M)
  apply (derivativeTail_square_integrable.const_mul (A ^ 2)).mono'
    ((spatialD_smooth j (spatialD_smooth k hf)).continuous.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  have hb : |spatialD j (spatialD k f) x| ≤ A * derivativeTail x :=
    scalar_hessian_entry_tail hf hB hM hfB hfM x j k
  have hA : 0 ≤ A * derivativeTail x :=
    mul_nonneg (by dsimp [A]; positivity) (derivativeTail_pos x).le
  have hs := (sq_le_sq₀ (abs_nonneg _) hA).mpr hb
  change ‖spatialD j (spatialD k f) x ^ 2‖ ≤ A ^ 2 * derivativeTail x ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (spatialD j (spatialD k f) x)]


end ForcedComputation.VelocityDetector

end

end OAI
