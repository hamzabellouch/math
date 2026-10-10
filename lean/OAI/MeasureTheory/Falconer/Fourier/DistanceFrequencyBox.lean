import OAI.MeasureTheory.Falconer.Fourier.DistanceSincKernel
import OAI.MeasureTheory.Falconer.Fourier.DistanceFourierDifference
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def distanceFrequencyBox (u : ℝ) : Measure ℝ := volume.restrict (Ioc (-u) u)

instance distanceFrequencyBox_finite (u : ℝ) : IsFiniteMeasure (distanceFrequencyBox u) := by
  unfold distanceFrequencyBox
  infer_instance

theorem distanceFrequencyBox_mass {u : ℝ} (hu : 0 ≤ u) :
    distanceFrequencyBox u univ = ENNReal.ofReal (2*u) := by
  simp only [distanceFrequencyBox,Measure.restrict_apply_univ,Real.volume_Ioc]
  apply (ENNReal.ofReal_eq_ofReal_iff (sub_nonneg.mpr (neg_le_self hu))
    (mul_nonneg (by norm_num) hu)).2
  ring

theorem distanceFrequencyBox_charFun {u : ℝ} (hu : 0 ≤ u) (s : ℝ) :
    charFun (distanceFrequencyBox u) s = ((2*u*Real.sinc (u*s):ℝ):ℂ) := by
  rw [charFun_apply_real]
  change (∫ r in Ioc (-u) u, Complex.exp ((s:ℂ)*r*Complex.I)) = _
  rw [← intervalIntegral.integral_of_le (by linarith : -u ≤ u)]
  simpa only [Complex.ofReal_mul,mul_comm (s:ℂ)] using interval_exp_eq_sinc u s

theorem distanceFrequencyBox_difference_charFun {u : ℝ} (hu : 0 ≤ u) (s : ℝ) :
    charFun (distanceDifferenceMeasure (distanceFrequencyBox u)) s =
      (((2*u)^2 * distanceSincKernel u s:ℝ):ℂ) := by
  rw [charFun_distanceDifferenceMeasure,distanceFrequencyBox_charFun hu,
    Complex.norm_real,Real.norm_eq_abs,← Complex.ofReal_pow,sq_abs]
  congr 1
  dsimp [distanceSincKernel]
  ring

theorem distanceFrequencyBox_difference_le_volume {u : ℝ} (hu : 0 ≤ u) :
    distanceDifferenceMeasure (distanceFrequencyBox u) ≤ ENNReal.ofReal (2*u) • volume := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [distanceDifferenceMeasure,Measure.map_apply (by fun_prop) hS,
    Measure.prod_apply (hS.preimage (by fun_prop))]
  calc
    _ ≤ ∫⁻ x, volume S ∂distanceFrequencyBox u := by
      apply lintegral_mono
      intro x
      calc
        _ ≤ volume ((fun y : ℝ => x-y) ⁻¹' S) := Measure.restrict_apply_le _ _
        _ = volume S := (volume.measurePreserving_sub_left x).measure_preimage hS.nullMeasurableSet
    _ = _ := by
      rw [lintegral_const,distanceFrequencyBox_mass hu,Measure.smul_apply,smul_eq_mul,mul_comm]

theorem distanceFrequencyBox_difference_supported {u : ℝ} :
    ∀ᵐ s ∂distanceDifferenceMeasure (distanceFrequencyBox u), s ∈ Icc (-2*u) (2*u) := by
  rw [distanceDifferenceMeasure,ae_map_iff (by fun_prop) (by measurability)]
  have hm : ∀ᵐ x ∂distanceFrequencyBox u, x ∈ Ioc (-u) u := ae_restrict_mem measurableSet_Ioc
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hm,
    Measure.quasiMeasurePreserving_snd.ae hm] with z hz₁ hz₂
  exact ⟨by linarith [hz₁.1,hz₂.2],by linarith [hz₁.2,hz₂.1]⟩

theorem distanceFrequencyBox_difference_le_band {u : ℝ} (hu : 0 ≤ u) :
    distanceDifferenceMeasure (distanceFrequencyBox u) ≤
      ENNReal.ofReal (2*u) • volume.restrict (Icc (-2*u) (2*u)) := by
  calc
    _ = (distanceDifferenceMeasure (distanceFrequencyBox u)).restrict (Icc (-2*u) (2*u)) :=
      (Measure.restrict_eq_self_of_ae_mem distanceFrequencyBox_difference_supported).symm
    _ ≤ (ENNReal.ofReal (2*u) • volume).restrict (Icc (-2*u) (2*u)) :=
      Measure.restrict_mono (Subset.refl _) (distanceFrequencyBox_difference_le_volume hu)
    _ = _ := Measure.restrict_smul _ _ _

end PlanarFalconer

end OAI
