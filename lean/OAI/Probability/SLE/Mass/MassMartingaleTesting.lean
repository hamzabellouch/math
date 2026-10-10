import OAI.Probability.SLE.Mass.MassUniquenessSeparation
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

namespace OAI

/-! Bounded predictable testing of the increments in the mass uniqueness proof. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

namespace SLEExactGauge

lemma massSeparationTest_continuous : Continuous massSeparationTest :=
  continuous_iff_continuousAt.mpr (fun x => (massSeparationTest_hasDerivAt x).continuousAt)

lemma massSeparationSlope_continuous : Continuous massSeparationSlope :=
  continuous_iff_continuousAt.mpr (fun x => (massSeparationSlope_hasDerivAt x).continuousAt)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}

omit [IsFiniteMeasure P] in
lemma martingale_mass_test_integrable (hM : Martingale M ℱ P) (t : ℝ≥0) :
    Integrable (fun ω => massSeparationTest (M t ω)) P := by
  apply ((hM.integrable t).norm.const_mul 2).mono'
    (massSeparationTest_continuous.comp_stronglyMeasurable
      ((hM.stronglyMeasurable t).mono (ℱ.le t))).aestronglyMeasurable
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs,massSeparationTest_zero,sub_zero] using
    massSeparationTest_lipschitz 0 (M t ω)

omit [IsFiniteMeasure P] in
lemma martingale_mass_weighted_increment_integrable (hM : Martingale M ℱ P)
    (s t : ℝ≥0) :
    Integrable (fun ω => massSeparationSlope (M s ω)*(M t ω-M s ω)) P := by
  exact ((hM.integrable t).sub (hM.integrable s)).bdd_mul
    (massSeparationSlope_continuous.comp_stronglyMeasurable
      ((hM.stronglyMeasurable s).mono (ℱ.le s))).aestronglyMeasurable
    (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using
      massSeparationSlope_abs_le (M s ω)))

lemma martingale_mass_weighted_increment_mean (hM : Martingale M ℱ P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, massSeparationSlope (M s ω)*(M t ω-M s ω) ∂P) = 0 := by
  have hg := (hM.integrable t).sub (hM.integrable s)
  have hfg := martingale_mass_weighted_increment_integrable hM s t
  have hCE : P[(fun ω => M t ω-M s ω) | ℱ s] =ᵐ[P] 0 := by
    have hsub := condExp_sub (hM.integrable t) (hM.integrable s) (ℱ s)
    have hs : P[M s | ℱ s] = M s :=
      condExp_of_stronglyMeasurable (ℱ.le s) (hM.stronglyMeasurable s) (hM.integrable s)
    filter_upwards [hsub,hM.condExp_ae_eq hst] with ω hω htω
    simp only [Pi.sub_apply,hs,htω,sub_self,Pi.zero_apply] at hω ⊢
    exact hω
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (massSeparationSlope_continuous.comp_stronglyMeasurable (hM.stronglyMeasurable s)) hfg hg
  calc
    _ = ∫ ω, P[(fun ω => massSeparationSlope (M s ω)*(M t ω-M s ω)) | ℱ s] ω ∂P :=
      (integral_condExp (ℱ.le s)).symm
    _ = 0 := by
      have he : P[(fun ω => massSeparationSlope (M s ω)*(M t ω-M s ω)) | ℱ s] =ᵐ[P] 0 := by
        filter_upwards [hpull,hCE] with ω hp hc
        change P[(fun ω => massSeparationSlope (M s ω)*(M t ω-M s ω)) | ℱ s] ω =
          massSeparationSlope (M s ω)*P[(fun ω => M t ω-M s ω) | ℱ s] ω at hp
        change P[(fun ω => M t ω-M s ω) | ℱ s] ω = 0 at hc
        simpa only [hc,mul_zero,Pi.zero_apply] using hp
      rw [integral_congr_ae he]
      simp

end SLEExactGauge

end

end OAI
