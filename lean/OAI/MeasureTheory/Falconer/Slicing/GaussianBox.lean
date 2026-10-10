import OAI.MeasureTheory.Falconer.Slicing.GaussianDensity

namespace OAI

/-! # Gaussian bounds for nonsingular systems of linear bands -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {j : ℕ}

noncomputable def coordinateBox (j : ℕ) (r : ℝ) : Set (Space j) :=
  {x | ∀ i, |x i| ≤ r}

theorem coordinateBox_measurable (r : ℝ) : MeasurableSet (coordinateBox j r) := by
  simp only [coordinateBox,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

theorem coordinateBox_volume {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space j)) (coordinateBox j r) = ENNReal.ofReal ((2*r)^j) := by
  rw [← (PiLp.volume_preserving_toLp (Fin j)).measure_preimage
    (coordinateBox_measurable r).nullMeasurableSet]
  have he : (@WithLp.toLp 2 (Fin j → ℝ)) ⁻¹' coordinateBox j r =
      Set.pi univ (fun _ : Fin j => Icc (-r) r) := by
    ext x
    simp [coordinateBox,abs_le,Pi.le_def,forall_and]
  rw [he,volume_pi_pi]
  simp only [Real.volume_Icc,sub_neg_eq_add,← two_mul,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*r)]

theorem gaussian_linear_bands (L : Space j →L[ℝ] Space j)
    (hL : LinearMap.det (L : Space j →ₗ[ℝ] Space j) ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space j) {x | ∀ i, |L x i| ≤ r} ≤
      ENNReal.ofReal (gaussianVolumeNormalization j*
        |(LinearMap.det (L : Space j →ₗ[ℝ] Space j))⁻¹| * (2*r)^j) := by
  have hc : 0 ≤ gaussianVolumeNormalization j := by unfold gaussianVolumeNormalization; positivity
  calc
    _ ≤ (ENNReal.ofReal (gaussianVolumeNormalization j) • (volume : Measure (Space j)))
        (L ⁻¹' coordinateBox j r) := standard_gaussian_le_volume _
    _ = _ := by
      rw [Measure.smul_apply,smul_eq_mul,Measure.addHaar_preimage_continuousLinearMap volume hL,
        coordinateBox_volume hr,← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by unfold gaussianVolumeNormalization; positivity)]
      congr 1
      ring

end Falconer

end OAI
