import OAI.Geometry.NodalSets.Coefficients.RealFiniteCoefficientL2Bound
import OAI.Geometry.NodalSets.Spectral.SphereEigenResolventForcing

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_half_cube_gradient_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ (z : SphereEnergyHilbert d) (k : Fin 4),
      MemLp (sphereChartDerivativeMap d p k z) 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))) ∧
      (∫ x in Yau.realCenteredCube 4 (1/2), ((sphereChartDerivativeMap d p k z) x)^2) ≤ C*‖z‖^2 := by
  obtain ⟨D,hD,hd⟩ := sphereChartDerivativeMap_bound d p
  refine ⟨D^2,sq_pos_of_pos hD,fun z k ↦ ?_⟩
  have hsub : Yau.realCenteredCube 4 (1/2) ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  have hmem := (Lp.memLp (sphereChartDerivativeMap d p k z)).mono_measure
    (Measure.restrict_mono hsub le_rfl)
  refine ⟨hmem,?_⟩
  have hmono := integral_mono_measure (Measure.restrict_mono hsub (le_refl volume))
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg ((sphereChartDerivativeMap d p k z) x)))
    (Lp.memLp (sphereChartDerivativeMap d p k z)).integrable_sq
  have hnorm : ‖sphereChartDerivativeMap d p k z‖^2 =
      ∫ x in realFinCube 4, ((sphereChartDerivativeMap d p k z) x)^2 := by
    simpa only [Lp.toLp_coeFn] using Yau.real_toLp_norm_sq _ (Lp.memLp (sphereChartDerivativeMap d p k z))
  rw [← hnorm] at hmono
  have hb := hd k z
  have hsq : ‖sphereChartDerivativeMap d p k z‖^2 ≤ (D*‖z‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [mul_pow] using hmono.trans hsq

theorem sphere_eigen_forcing_derivative_bound (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (k : Fin 4) :
    ∃ C > 0, ∀ f : SphereWeightedL2 d,
      MemLp (sphereEigenForcingDerivative d p mu f k) 2
        (volume.restrict (Yau.realCenteredCube 4 (1/2))) ∧
      (∫ x in Yau.realCenteredCube 4 (1/2), (sphereEigenForcingDerivative d p mu f k x)^2) ≤
        C*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
  let Q := Yau.realCenteredCube 4 (1/2)
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 (1/2)
  have ha : ContDiff ℝ ∞ (sphereEigenForcingCoefficient d p mu) :=
    contDiff_const.mul (roundCoordDensity_smooth.mul hrho)
  obtain ⟨A,hA,hAb⟩ := Yau.real_compact_multiplier_bound hQ _ ha.continuous
  obtain ⟨B,hB,hBb⟩ := Yau.real_compact_multiplier_bound hQ
    (fun x ↦ Yau.coordPartial (sphereEigenForcingCoefficient d p mu) x k)
    (Yau.real_coordPartial_smooth _ ha k).continuous
  obtain ⟨D,hD,hd⟩ := sphere_half_cube_gradient_bound d p
  obtain ⟨E,hE,he⟩ := sphereWeightedL2_compact_chart_bound d p hQ
  refine ⟨2*(A*D+B*E),by positivity,fun f ↦ ?_⟩
  have h1 := hAb (sphereChartDerivativeMap d p k (sphereWeakSolution d f)) (hd _ k).1
  have h2 := hBb (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)) (he _).1
  refine ⟨h1.1.add h2.1,?_⟩
  have hadd := Yau.real_L2_add_square_bound (volume.restrict Q) _ _ h1.1 h2.1
  have hn : ‖sphereL2Resolvent d f‖ ≤ ‖f‖ := by
    have ht := (sphereL2Resolvent d).le_opNorm f
    exact ht.trans (by simpa using mul_le_mul_of_nonneg_right (sphereL2Resolvent_norm_le d) (norm_nonneg f))
  have hn2 : ‖sphereL2Resolvent d f‖^2 ≤ ‖f‖^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h1b := h1.2.trans (mul_le_mul_of_nonneg_left (hd _ k).2 hA.le)
  have h2b := h2.2.trans (mul_le_mul_of_nonneg_left ((he _).2.trans
    (mul_le_mul_of_nonneg_left hn2 hE.le)) hB.le)
  change (∫ x in Q, (sphereEigenForcingDerivative d p mu f k x)^2) ≤ _
  dsimp only [sphereEigenForcingDerivative]
  nlinarith [h1b,h2b,mul_nonneg (mul_nonneg hA.le hD.le) (sq_nonneg ‖f‖),
    mul_nonneg (mul_nonneg hB.le hE.le) (sq_nonneg ‖sphereWeakSolution d f‖)]

end
end Yau.Target

end OAI
