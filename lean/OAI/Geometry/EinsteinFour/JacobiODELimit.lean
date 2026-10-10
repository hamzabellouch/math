import OAI.Geometry.EinsteinFour.JacobiODEPositivity
import OAI.Geometry.EinsteinFour.JacobiDirichletLimit

namespace OAI

/-! Determinant convergence from the same preconjugate Jacobi ODE data. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RegularJacobi

variable {t : ℝ} (d : RegularJacobi t)

theorem endpoint_position_tendsto (ht : 0 < t) :
    Tendsto (fun N : ℕ =>
      discretePosition (meshCurvature d.R t N) (meshStep t N) (N + 1))
      atTop (nhds (d.J t)) := by
  have hnorm : Tendsto (fun N : ℕ =>
      ‖relativeDiscretePosition (meshCurvature d.R t N) (meshStep t N) (N + 1) -
        normalizedJacobi d.J t‖) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ d.positionError_tendsto
    filter_upwards [d.uniform_errors ht] with N hN
    have htmesh : ((N + 1 : ℕ) : ℝ) * meshStep t N = t := by
      simp only [meshStep, Nat.cast_add, Nat.cast_one]
      field_simp
    simpa only [htmesh] using hN.1 (N + 1) le_rfl
  have hb := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  have hc := hb.const_smul t
  have hid (N : ℕ) :
      t • relativeDiscretePosition (meshCurvature d.R t N) (meshStep t N) (N + 1) =
        discretePosition (meshCurvature d.R t N) (meshStep t N) (N + 1) := by
    rw [relativeDiscretePosition_pos _ _ (Nat.succ_pos N)]
    have htmesh : ((N + 1 : ℕ) : ℝ) * meshStep t N = t := by
      simp only [meshStep, Nat.cast_add, Nat.cast_one]
      field_simp
    rw [htmesh, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  simpa only [hid, normalizedJacobi_pos d.initial_position ht.ne', smul_smul,
    mul_inv_cancel₀ ht.ne', one_smul] using hc

theorem normalizedDiscrete_eventually_isUnit (ht : 0 < t)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s)) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 1 ≤ i → i ≤ N + 1 →
      IsUnit (normalizedDiscrete (meshCurvature d.R t N) (meshStep t N) i).det := by
  have hcJ : ContinuousOn d.J (Set.Icc 0 t) := fun s hs =>
    (d.position_derivative s hs).continuousAt.continuousWithinAt
  have hd0 : HasDerivAt d.J 1 0 := by
    simpa only [d.initial_velocity] using d.position_derivative 0 ⟨le_rfl, ht.le⟩
  obtain ⟨K, _, hK⟩ := eventually_mesh_inverse_bounds ht.le
    (normalizedJacobi_continuousOn hcJ hd0)
    (normalizedJacobi_isUnit d.initial_position hd0 hpre) d.positionError_tendsto
    ((d.uniform_errors ht).mono fun _ h => h.1)
  filter_upwards [hK] with N hN i hi0 hiN
  have hh : meshStep t N ≠ 0 := ne_of_gt (div_pos ht (by positivity))
  have hbi := (hN i hiN).1
  rw [relativeDiscretePosition_pos _ _ (by omega)] at hbi
  have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  have hx := isUnit_of_divided_time (mul_ne_zero hi' hh) hbi
  have hs : IsUnit (algebraMap ℝ NormalMatrix (meshStep t N)⁻¹) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hh)).map (algebraMap ℝ NormalMatrix)
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  simpa only [normalizedDiscrete, Algebra.smul_def] using hs.mul hx

theorem curvatureDirichlet_det_tendsto (ht : 0 < t)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s)) :
    Tendsto (fun N : ℕ => (meshStep t N) ^ 3 *
      (curvatureDirichlet t (fun i : Fin N =>
        d.R (((i.val + 1 : ℕ) : ℝ) * meshStep t N) - 1)).det)
      atTop (nhds (d.J t).det) := by
  exact curvatureDirichlet_det_tendsto_of_position_tendsto ht.ne'
    (meshCurvature d.R t) (fun N i => d.symmetric _) (d.J t)
    (d.normalizedDiscrete_eventually_isUnit ht hpre) (d.endpoint_position_tendsto ht)

end RegularJacobi

end

end PositiveEinsteinFour.Jacobi

end OAI
