import OAI.Geometry.EinsteinFour.FlatGreenDeterminant
import OAI.Geometry.EinsteinFour.JacobiODELimit

namespace OAI

/-! The flat-kernel determinants converge without a preconjugacy premise. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
open scoped Matrix.Norms.L2Operator
noncomputable section

namespace RegularJacobi
variable {t : ℝ} (d : RegularJacobi t)

theorem flat_kernel_determinant_tendsto (ht : 0 < t)
    (htop : t < Real.pi / Real.sqrt 3)
    (hR : ∀ s, (d.R s).PosSemidef ∧ (d.R s).trace = 3) :
    Tendsto (fun N : ℕ => (1 - curvatureKernel (scaledFlatGreen t N)
      (fun i => d.R (((i.val + 1 : ℕ) : ℝ) * meshStep t N))).det)
      atTop (nhds ((d.J t).det / t ^ 3)) := by
  have hx := (continuous_id.matrix_det.tendsto (d.J t)).comp
    (d.endpoint_position_tendsto ht)
  apply (hx.div_const (t ^ 3)).congr'
  filter_upwards [scaledFlatGreen_eventually_below_one ht.le htop] with N hN
  have hp := flat_curvatureDirichlet_posDef t
    (fun i : Fin N => d.R (((i.val + 1 : ℕ) : ℝ) * meshStep t N))
    (fun i => hR _) hN
  have he := flatGreen_endpoint_det ht.ne' (meshCurvature d.R t N)
    (fun i => d.symmetric _) hp
  change (discretePosition (meshCurvature d.R t N) (meshStep t N) (N + 1)).det / t ^ 3 = _
  simp only [meshStep, meshCurvature] at he ⊢
  rw [← he]
  field_simp

end RegularJacobi
end
end PositiveEinsteinFour.Jacobi

end OAI
