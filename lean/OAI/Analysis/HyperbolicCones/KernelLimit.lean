import OAI.Analysis.HyperbolicCones.SpectralContinuity
import OAI.Analysis.HyperbolicCones.InverseOrder

namespace OAI

/-! The inverse-square-root kernel limit for every finite positive semidefinite matrix. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology
namespace Paper256

theorem inverseSquareRoot_affine_eq_cfc {n : ℕ} (H : Sym n) (t : ℝ) :
    inverseSquareRoot (1 + (t - 1) • H) =
      cfc (fun x : ℝ => (Real.sqrt (1 + (t - 1) * x))⁻¹) (H : Mat n ℝ) := by
  have haff : cfc (fun x : ℝ => 1 + (t - 1) * x) (H : Mat n ℝ) =
      ((1 + (t - 1) • H : Sym n) : Mat n ℝ) := by
    simpa using matrix_cfc_affine H 1 (t - 1)
  have hcomp := cfc_comp (fun x : ℝ => (Real.sqrt x)⁻¹)
    (fun x : ℝ => 1 + (t - 1) * x) (H : Mat n ℝ) H.property
    ((H.val.finite_real_spectrum.image _).continuousOn _)
    (H.val.finite_real_spectrum.continuousOn _)
  rw [haff] at hcomp
  exact (inverseSquareRoot_eq_cfc _).trans hcomp.symm

theorem inverseSquareRoot_affine_tendsto {n : ℕ} (H : Sym n)
    (hH : (H : Mat n ℝ).PosSemidef) :
    Tendsto (fun t : ℝ => inverseSquareRoot (1 + (t - 1) • H)) atTop
      (𝓝 (kernelProjection (H : Mat n ℝ))) := by
  have hc := matrix_cfc_tendsto (H : Mat n ℝ) H.property
    (fun t x : ℝ => (Real.sqrt (1 + (t - 1) * x))⁻¹)
    (fun x : ℝ => if x = 0 then 1 else 0)
    (fun i => inverse_sqrt_affine_scalar_tendsto _ (hH.eigenvalues_nonneg i))
  simpa only [← inverseSquareRoot_affine_eq_cfc, ← kernelProjection_eq_cfc] using hc

theorem inverseSquareRoot_kernel_limit (n : ℕ) (H : Sym n)
    (hH : (H : Mat n ℝ).PosSemidef) :
    Tendsto (fun t : ℝ => operatorNorm
      (inverseSquareRoot (1 + (t - 1) • H) - kernelProjection (H : Mat n ℝ)))
      atTop (𝓝 0) := by
  have h := ((inverseSquareRoot_affine_tendsto H hH).sub_const
    (kernelProjection (H : Mat n ℝ))).norm
  have hop (A : Mat n ℝ) : operatorNorm A = ‖A‖ := (Matrix.l2_opNorm_def A).symm
  simpa only [hop, sub_self, norm_zero] using h

end Paper256

end

end OAI
