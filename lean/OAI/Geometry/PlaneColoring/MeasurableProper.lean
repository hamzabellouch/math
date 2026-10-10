import OAI.Geometry.PlaneColoring.Basic

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem160

@[continuity, fun_prop]
theorem continuous_circleDir : Continuous circleDir := by
  unfold circleDir
  fun_prop

@[fun_prop]
theorem measurable_circleDir : Measurable circleDir :=
  continuous_circleDir.measurable

instance normalizedAngleMeasure_isProbabilityMeasure :
    IsProbabilityMeasure normalizedAngleMeasure where
  measure_univ := by
    have hpos : 0 < (2 : ℝ) * Real.pi := by positivity
    simp only [normalizedAngleMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
      Real.volume_Ico, sub_zero, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hpos))
      ENNReal.ofReal_ne_top

instance circleMeasure_isProbabilityMeasure : IsProbabilityMeasure circleMeasure :=
  inferInstanceAs (IsProbabilityMeasure (Measure.map circleDir normalizedAngleMeasure))

@[simp]
theorem norm_circleDir (t : ℝ) : ‖circleDir t‖ = 1 := by
  have h : ‖circleDir t‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [circleDir, Fin.sum_univ_two]
  nlinarith [norm_nonneg (circleDir t)]

theorem ae_circleMeasure_norm : ∀ᵐ u ∂circleMeasure, ‖u‖ = 1 := by
  unfold circleMeasure
  rw [ae_map_iff measurable_circleDir.aemeasurable]
  · exact Filter.Eventually.of_forall norm_circleDir
  · exact isClosed_eq continuous_norm continuous_const |>.measurableSet

theorem ae_weakPairMeasure_unit (R : ℝ) :
    ∀ᵐ p ∂weakPairMeasure R, ‖p.2‖ = 1 := by
  exact Measure.quasiMeasurePreserving_snd.ae ae_circleMeasure_norm

theorem weakMeasurableColoring_of_aemeasurable_proper {k : ℕ}
    (c : Plane → Fin k) (hc : AEMeasurable c volume)
    (hproper : ∀ x y : Plane, dist x y = 1 → c x ≠ c y) :
    WeakMeasurableColoring k := by
  refine ⟨c, hc, ?_⟩
  intro R hR
  apply Finset.sum_eq_zero
  intro i hi
  apply measure_mono_null (t := {p : Plane × Plane | ‖p.2‖ ≠ 1})
  · intro p hp hnorm
    have hd : dist p.1 (p.1 + p.2) = 1 := by
      simpa [dist_eq_norm] using hnorm
    exact hproper _ _ hd (hp.1.trans hp.2.symm)
  · exact ae_iff.mp (ae_weakPairMeasure_unit R)

end Problem160

end

end OAI
