import OAI.Geometry.NodalSets.Spectral.SphereResolventSpectrum

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold
open scoped ContDiff
noncomputable section
local instance sphereVariationalResolventMeasurable : MeasurableSpace Base := borel Base
local instance sphereVariationalResolventBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_variational_eigenvalue_nonneg (d : SphereEnergyData) (lam : ℝ)
    (z : SphereEnergyHilbert d) (hz : sphereEnergyL2Map d z ≠ 0)
    (he : ∀ v, sphereCompletedDirichlet d z v =
      lam*inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d v)) : 0 ≤ lam := by
  have h := sphereCompletedDirichlet_nonneg d z
  rw [he z,real_inner_self_eq_norm_sq] at h
  exact (mul_nonneg_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hz))).mp h

theorem sphere_variational_eigen_to_resolvent (d : SphereEnergyData) (lam : ℝ)
    (z : SphereEnergyHilbert d) (hz : sphereEnergyL2Map d z ≠ 0)
    (he : ∀ v, sphereCompletedDirichlet d z v =
      lam*inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d v)) :
    z = (lam+1) • sphereWeakSolution d (sphereEnergyL2Map d z) ∧
    sphereL2Resolvent d (sphereEnergyL2Map d z) = (lam+1)⁻¹ • sphereEnergyL2Map d z := by
  have hlam : 0 < lam+1 := by linarith [sphere_variational_eigenvalue_nonneg d lam z hz he]
  have heq : z = (lam+1) • sphereWeakSolution d (sphereEnergyL2Map d z) := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_smul_left_eq_smul,smul_eq_mul,sphereWeakSolution_spec]
    have h := he v
    dsimp [sphereCompletedDirichlet] at h
    linarith
  refine ⟨heq,?_⟩
  have h := congrArg (sphereEnergyL2Map d) heq
  rw [map_smul] at h
  change sphereEnergyL2Map d z = (lam+1) • sphereL2Resolvent d (sphereEnergyL2Map d z) at h
  conv_rhs => rw [h,smul_smul,inv_mul_cancel₀ hlam.ne',one_smul]

theorem sphere_smooth_intrinsic_eigen_to_variational (d : SphereEnergyData)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (u : SphereEnergySmooth d) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator d.tensor d.density (SphereEnergySmooth.toSmooth d u) p z =
      lam*((SphereEnergySmooth.toSmooth d u : Base → ℝ)) ((extChartAt (𝓡 4) p).symm z)) :
    ∀ v : SphereEnergyHilbert d,
      sphereCompletedDirichlet d (sphereEnergyToCompletion d u) v =
        lam*inner ℝ (sphereEnergyL2Map d (sphereEnergyToCompletion d u)) (sphereEnergyL2Map d v) := by
  intro v
  apply (sphereEnergyToCompletion_dense d).induction_on
    (p := fun v ↦ sphereCompletedDirichlet d (sphereEnergyToCompletion d u) v =
      lam*inner ℝ (sphereEnergyL2Map d (sphereEnergyToCompletion d u)) (sphereEnergyL2Map d v)) v
  · apply isClosed_eq
    · exact (continuous_const.inner continuous_id).sub
        (continuous_const.inner (sphereEnergyL2Map d).continuous)
    · fun_prop
  · intro w
    rw [sphereCompletedDirichlet_coe,sphereEnergyL2Map_coe,sphereEnergyL2Map_coe]
    have hinner : inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Linear d w) =
        sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d w) :=
      sphereWeightedToLp_inner _ d.continuous (fun x ↦ (d.positive x).le) _ _
        (SphereEnergySmooth.toSmooth d u).property.continuous (SphereEnergySmooth.toSmooth d w).property.continuous
    rw [hinner,sphereDirichletForm_symm d.tensor d.symm]
    have h := (intrinsic_green_eigenfunction_test d.tensor d.smooth d.symm d.pos d.density hr d.positive
      (SphereEnergySmooth.toSmooth d w) (SphereEnergySmooth.toSmooth d u)
      (SphereEnergySmooth.toSmooth d w).property (SphereEnergySmooth.toSmooth d u).property lam he).2.2
    simpa only [sphereDirichletForm,sphereWeightedPairing_symm d.density (SphereEnergySmooth.toSmooth d w)
      (SphereEnergySmooth.toSmooth d u)] using h

end
end Yau.Target

end OAI
