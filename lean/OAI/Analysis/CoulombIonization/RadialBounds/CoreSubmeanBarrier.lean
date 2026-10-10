import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.RetainedFieldIdentity
import OAI.Analysis.CoulombIonization.FormDomain.ShiftedCoulombIntegrable

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombAnalysis

lemma radial_translatedDensity_core_le {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {η : Space → ℝ} (hm : Measurable η)
    {R B : ℝ} (hR : 0 ≤ R) (hn : ∀ x, 0 ≤ η x)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B)
    (hr : IsRadial η) (h1 : ∫ x : Space, η x = 1) (y : Space) :
    coreDensityInteraction ψ (translatedDensity η y) ≤ coreCoulombAt ψ y := by
  have hsupport : Function.support η ⊆ closedBall 0 R :=
    fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hs x hx
  have hi := bounded_compact_integrable hm (isCompact_closedBall _ _) hsupport hb
  have hp := bounded_compact_memLp hm (isCompact_closedBall _ _) hsupport hb (5/3 : ENNReal)
  have htm := translatedDensity_measurable hm y
  have hts := translatedDensity_support hs y
  have hti := bounded_compact_integrable htm (isCompact_closedBall _ _) hts (fun z => hb (z-y))
  have htp := bounded_compact_memLp htm (isCompact_closedBall _ _) hts (fun z => hb (z-y)) (5/3 : ENNReal)
  obtain ⟨C,hC⟩ := compact_support_potential_bounded hti htp (isCompact_closedBall y R) hts
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro i _
  apply integral_mono_ae
    (core_bounded_potential_integrable hψ (tfPotential_continuous hti htp) hC s i)
    (hψ.shifted_nuclear_integrable s i y)
  filter_upwards [Measure.ae_eval_ne (fun _ : Fin N => (volume : Measure Space)) i y] with x hx
  rw [potential_translatedDensity]
  have he := radial_potential_le_point hi hp hn hr hR hs (sub_ne_zero.mpr hx)
  rw [h1] at he
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left he (sq_nonneg ‖ψ.value s x‖)

theorem normalizedCoreField_radial_submean {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {η : Space → ℝ} (hm : Measurable η)
    {R B : ℝ} (hR : 0 < R) (hn : ∀ x, 0 ≤ η x)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B)
    (hr : IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (y : Space) (hnuc : R ≤ ‖y‖) (Z lam : ℝ) :
    normalizedCoreField Z lam ψ y ≤
      ∫ z, normalizedCoreField Z lam ψ z*η (z-y) := by
  change _ ≤ ∫ z, normalizedCoreField Z lam ψ z*translatedDensity η y z
  rw [normalizedCoreField_pairing hψ (translatedDensity_measurable hm y)
    (isCompact_closedBall y R) (translatedDensity_support hs y) (fun z => hb (z-y)),
    radial_translatedDensity_potential hm hR hs hb hr h1 y 0
      (by simpa only [zero_sub,norm_neg] using hnuc),
    translatedDensity_mass,h1,zero_sub,norm_neg,mul_one]
  apply sub_le_sub_right
  apply div_le_div_of_nonneg_right _ (formMass_nonneg ψ)
  rw [mul_one_div]
  exact sub_le_sub_left (radial_translatedDensity_core_le hψ hm hR.le hn hs hb hr h1 y) _

end CoulombAtom

end

end OAI
