import Mathlib
import OAI.Analysis.CoulombIonization.Variational.Inner
import OAI.Analysis.CoulombIonization.Fermionic.WeightedCoreStatistics

namespace OAI

open MeasureTheory Filter Set
open scoped BigOperators
noncomputable section
namespace CoulombAtom

def coulombTailWeight (h : ℝ) (a : Space) : ℝ := if h < ‖a‖ then ‖a‖⁻¹ else 0
lemma coulombTailWeight_measurable (h : ℝ) : Measurable (coulombTailWeight h) :=
  continuous_norm.measurable.inv.ite (measurableSet_lt measurable_const continuous_norm.measurable) measurable_const
lemma coulombTailWeight_nonneg (h : ℝ) (a : Space) : 0 ≤ coulombTailWeight h a := by
  unfold coulombTailWeight; split_ifs <;> positivity
lemma coulombTailWeight_le {h : ℝ} (hh : 0 < h) (a : Space) : coulombTailWeight h a ≤ 1/h := by
  unfold coulombTailWeight
  split_ifs with ha
  · simpa only [one_div] using inv_anti₀ hh ha.le
  · positivity

lemma rawWeightedFirst_le_sqrt {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    rawFormPair psi (rawWeightedCount f) ≤ Real.sqrt (rawWeightedMoment psi f)*Real.sqrt (formMass psi) := by
  have hc := weighted_sum_integral_cauchy (fun _ : Spins N => volume)
    (fun s x => ‖psi.value s x‖^2) (fun _ => rawWeightedCount f) (fun _ _ => 1)
    (fun _ _ => sq_nonneg _)
    (fun s => rawFormPair_integrable hpsi ((rawWeightedCount_measurable hm).pow_const 2)
      (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn x) (rawWeightedCount_le hb x)) s)
    (fun s => by simpa only [one_pow,one_mul] using (hpsi.1 s).norm.integrable_sq)
    (fun s => by
      simpa only [mul_one] using (rawFormPair_integrable hpsi (rawWeightedCount_measurable hm)
        (fun x => by rw [Real.norm_of_nonneg (rawWeightedCount_nonneg hn x)]; exact rawWeightedCount_le hb x) s))
  simpa only [mul_one,one_pow,one_mul,rawFormPair,rawWeightedMoment,formMass] using hc

lemma actual_tail_eq_raw {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    {h : ℝ} (hh : 0 < h) :
    (∫ a, ‖a‖⁻¹ ∂(actualParticleSource psi).restrict {a | h < ‖a‖}) =
      rawFormPair psi (rawWeightedCount (coulombTailWeight h))/formMass psi := by
  let f := coulombTailWeight h
  have hm : Measurable f := coulombTailWeight_measurable h
  have hn : ∀ z, 0 ≤ f z := coulombTailWeight_nonneg h
  have hb : ∀ z, f z ≤ 1/h := coulombTailWeight_le hh
  let : IsFiniteMeasure (formRawLaw psi) := formRawLaw_finite hpsi
  have hi (i : Fin N) : Integrable (fun x : Configuration N => f (x i)) (formRawLaw psi) := by
    apply (integrable_const (1/h)).mono' (hm.comp (measurable_pi_apply i)).aestronglyMeasurable
    exact ae_of_all _ (fun x => by change ‖f (x i)‖ ≤ _; rw [Real.norm_of_nonneg (hn _)]; exact hb _)
  have hp := rawOneParticleLaw_pairing (formRawLaw psi) hm hi
  have hr := rawFormPair_eq_integral hpsi (rawWeightedCount_measurable hm)
    (fun x => by rw [Real.norm_of_nonneg (rawWeightedCount_nonneg hn x)]; exact rawWeightedCount_le hb x)
  have hind : (fun a : Space => ({a | h < ‖a‖} : Set Space).indicator (fun a => ‖a‖⁻¹) a) = f := rfl
  rw [←integral_indicator (measurableSet_lt measurable_const continuous_norm.measurable),hind]
  simp only [actualParticleSource,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (formMass_nonneg psi)),smul_eq_mul]
  rw [hp]
  change (formMass psi)⁻¹*(∫ x, rawWeightedCount f x ∂formRawLaw psi) = _
  rw [←hr]
  ring

theorem actual_tail_square_le {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    {h : ℝ} (hh : 0 < h) :
    (∫ a, ‖a‖⁻¹ ∂(actualParticleSource psi).restrict {a | h < ‖a‖})^2*formMass psi ≤
      rawWeightedMoment psi (coulombTailWeight h) := by
  rw [actual_tail_eq_raw hpsi hh]
  by_cases hm : formMass psi = 0
  · simp only [hm,mul_zero]; exact rawWeightedMoment_nonneg _ _
  have hm' : 0 < formMass psi := lt_of_le_of_ne (formMass_nonneg psi) (Ne.symm hm)
  have hn : 0 ≤ rawFormPair psi (rawWeightedCount (coulombTailWeight h)) :=
    Finset.sum_nonneg (fun s _ => integral_nonneg (fun x =>
      mul_nonneg (rawWeightedCount_nonneg (coulombTailWeight_nonneg h) x) (sq_nonneg _)))
  have hc := pow_le_pow_left₀ hn
    (rawWeightedFirst_le_sqrt hpsi (coulombTailWeight_measurable h)
      (coulombTailWeight_nonneg h) (coulombTailWeight_le hh)) 2
  rw [mul_pow,Real.sq_sqrt (rawWeightedMoment_nonneg _ _),Real.sq_sqrt hm'.le] at hc
  have he : (rawFormPair psi (rawWeightedCount (coulombTailWeight h))/formMass psi)^2*formMass psi =
      (rawFormPair psi (rawWeightedCount (coulombTailWeight h)))^2/formMass psi := by field_simp
  rw [he]
  exact (div_le_iff₀ hm').2 hc

namespace CoreObservationEnsemble
 theorem observeCells_tailMoment (E : CoreObservationEnsemble) (ys : List Space)
    {h : ℝ} (hh : 0 < h) :
    (E.observeCells ys).weightedMoment (coulombTailWeight h) ≤ E.weightedMoment (coulombTailWeight h) :=
  E.observeCells_weightedMoment ys (coulombTailWeight_measurable h)
    (coulombTailWeight_nonneg h) (coulombTailWeight_le hh)
end CoreObservationEnsemble
end CoulombAtom

end

end OAI
