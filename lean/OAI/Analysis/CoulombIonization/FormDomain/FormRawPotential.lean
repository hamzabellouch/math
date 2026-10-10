import Mathlib
import OAI.Analysis.CoulombIonization.Variational.IntegrableCutTower

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom

def rawPotential {N : ℕ} (y : Space) (x : Configuration N) : ℝ := ∑ i, 1/‖x i-y‖

lemma rawPotential_nonneg {N : ℕ} (y : Space) (x : Configuration N) : 0 ≤ rawPotential y x :=
  Finset.sum_nonneg (fun _ _ => by positivity)

lemma rawPotential_measurable {N : ℕ} (y : Space) : Measurable (rawPotential (N := N) y) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.div (configuration_distance_measurable y i))

lemma formRawLaw_integrable_iff {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {f : Configuration N → ℝ} :
    Integrable f (formRawLaw ψ) ↔ Integrable (fun x => formRawDensity ψ x*f x) := by
  rw [formRawLaw,integrable_withDensity_iff_integrable_smul₀'
    (formRawDensity_integrable hψ).aemeasurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (formRawDensity_nonneg ψ _),smul_eq_mul]

lemma rawPotential_form_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) (y : Space) :
    Integrable (rawPotential y) (formRawLaw ψ) := by
  rw [formRawLaw_integrable_iff hψ]
  simp only [formRawDensity,rawPotential,Finset.sum_mul,Finset.mul_sum]
  apply integrable_finsetSum
  intro s _
  apply integrable_finsetSum
  intro i _
  simpa only [mul_one_div] using hψ.shifted_nuclear_integrable i s y

lemma rawLocalPotential_le_raw {N : ℕ} (y : Space) (q : ℝ) (x : Configuration N) :
    rawLocalPotential y q x ≤ rawPotential y x := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · positivity

lemma rawLocalPotential_form_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) (q : ℝ) : Integrable (rawLocalPotential y q) (formRawLaw ψ) := by
  apply (rawPotential_form_integrable hψ y).mono' (rawLocalPotential_measurable N y q).aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_of_nonneg (rawLocalPotential_nonneg y q x)] using
    (rawLocalPotential_le_raw y q x))

lemma formRawLaw_ae_no_poles {N : ℕ} (ψ : FormVector N) (y : Space) :
    ∀ᵐ x ∂formRawLaw ψ, ∀ i, x i ≠ y := by
  apply (withDensity_absolutelyContinuous volume _).ae_le
  exact ae_all_iff.mpr (fun i => Measure.ae_eval_ne (fun _ : Fin N => (volume : Measure Space)) i y)

end CoulombAtom

end

end OAI
