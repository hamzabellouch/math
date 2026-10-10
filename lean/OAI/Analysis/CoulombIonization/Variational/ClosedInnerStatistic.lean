import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.dShellInnerField
import OAI.Analysis.CoulombIonization.Variational.Inner
import OAI.Analysis.CoulombIonization.Fermionic.WeightedCoreStatistics

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators
noncomputable section
namespace CoulombAtom

def innerParticleWeight (h : ℝ) (y a : Space) : ℝ := if ‖a‖ ≤ h then ‖y-a‖⁻¹ else 0
lemma innerParticleWeight_measurable (h : ℝ) (y : Space) : Measurable (innerParticleWeight h y) :=
  ((continuous_const.sub continuous_id).norm.measurable.inv).ite
    (measurableSet_le continuous_norm.measurable measurable_const) measurable_const
lemma innerParticleWeight_nonneg (h : ℝ) (y a : Space) : 0 ≤ innerParticleWeight h y a := by
  unfold innerParticleWeight; split_ifs <;> positivity
lemma innerParticleWeight_le {h d : ℝ} (hd : 0 < d) {y : Space} (hy : h+d ≤ ‖y‖) (a : Space) :
    innerParticleWeight h y a ≤ 1/d := by
  unfold innerParticleWeight
  split_ifs with ha
  · have hn := norm_le_norm_sub_add y a
    have hh : d ≤ ‖y-a‖ := by linarith
    simpa only [one_div] using inv_anti₀ hd hh
  · positivity

lemma sourcePotential_actualInnerSource_raw {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {h d : ℝ} (hd : 0 < d) {y : Space} (hy : h+d ≤ ‖y‖) :
    sourcePotential (actualInnerSource psi h) y =
      rawFormPair psi (rawWeightedCount (innerParticleWeight h y))/formMass psi := by
  let f := innerParticleWeight h y
  have hm : Measurable f := innerParticleWeight_measurable h y
  have hn : ∀ z, 0 ≤ f z := innerParticleWeight_nonneg h y
  have hb : ∀ z, f z ≤ 1/d := innerParticleWeight_le hd hy
  let : IsFiniteMeasure (formRawLaw psi) := formRawLaw_finite hpsi
  have hi (i : Fin N) : Integrable (fun x : Configuration N => f (x i)) (formRawLaw psi) := by
    apply (integrable_const (1/d)).mono' (hm.comp (measurable_pi_apply i)).aestronglyMeasurable
    exact ae_of_all _ (fun x => by change ‖f (x i)‖ ≤ _; rw [Real.norm_of_nonneg (hn _)]; exact hb _)
  have hp := rawOneParticleLaw_pairing (formRawLaw psi) hm hi
  have hr := rawFormPair_eq_integral hpsi (rawWeightedCount_measurable hm)
    (fun x => by rw [Real.norm_of_nonneg (rawWeightedCount_nonneg hn x)]; exact rawWeightedCount_le hb x)
  unfold sourcePotential actualInnerSource
  rw [←integral_indicator (measurableSet_le continuous_norm.measurable measurable_const)]
  change (∫ a, f a ∂actualParticleSource psi) = _
  simp only [actualParticleSource,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (formMass_nonneg psi)),smul_eq_mul]
  rw [hp]
  change (formMass psi)⁻¹*(∫ x, rawWeightedCount f x ∂formRawLaw psi) = _
  rw [←hr]
  ring

def closedRawInnerField {N : ℕ} (Z h : ℝ) (x : Configuration N) (y : Space) : ℝ :=
  Z/‖y‖-rawWeightedCount (innerParticleWeight h y) x

lemma closedRawInnerField_measurable (N : ℕ) (Z h : ℝ) :
    Measurable (fun xy : Configuration N × Space => closedRawInnerField Z h xy.1 xy.2) := by
  unfold closedRawInnerField rawWeightedCount innerParticleWeight
  apply Measurable.sub (measurable_const.div measurable_snd.norm)
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_snd.sub ((measurable_pi_apply i).comp measurable_fst)).norm.inv).ite
    (measurableSet_le (((measurable_pi_apply i).comp measurable_fst).norm) measurable_const) measurable_const

lemma closedRawInnerField_bound {N : ℕ} (Z : ℝ) {h a : ℝ} (ha : 0 < a) (hh : h+a ≤ 2*a)
    {y : Space} (hy : 2*a ≤ ‖y‖) (x : Configuration N) :
    ‖closedRawInnerField Z h x y‖ ≤ |Z|/(2*a)+(N:ℝ)/a := by
  have hn : 0 ≤ rawWeightedCount (innerParticleWeight h y) x :=
    rawWeightedCount_nonneg (innerParticleWeight_nonneg h y) x
  have hb := rawWeightedCount_le (innerParticleWeight_le ha (hh.trans hy)) x
  calc
    _ ≤ ‖Z/‖y‖‖+‖rawWeightedCount (innerParticleWeight h y) x‖ := norm_sub_le _ _
    _ = |Z|/‖y‖+rawWeightedCount (innerParticleWeight h y) x := by
      rw [norm_div,Real.norm_eq_abs,Real.norm_of_nonneg (norm_nonneg y),Real.norm_of_nonneg hn]
    _ ≤ |Z|/(2*a)+(N:ℝ)/a := by
      exact add_le_add (div_le_div_of_nonneg_left (abs_nonneg Z) (by positivity) hy) (by simpa only [mul_one_div] using hb)

lemma rawFormPair_closedRawInnerField {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {Z h d : ℝ} (hd : 0 < d) {y : Space} (hy : h+d ≤ ‖y‖)
    (hm : formMass psi ≠ 0) :
    rawFormPair psi (fun x => closedRawInnerField Z h x y) =
      sourceField Z (actualInnerSource psi h) y*formMass psi := by
  have hb (x : Configuration N) : ‖rawWeightedCount (innerParticleWeight h y) x‖ ≤ (N:ℝ)*(1/d) := by
    rw [Real.norm_of_nonneg (rawWeightedCount_nonneg (innerParticleWeight_nonneg h y) x)]
    exact rawWeightedCount_le (innerParticleWeight_le hd hy) x
  have hi (s : Spins N) := rawFormPair_integrable hpsi
    (rawWeightedCount_measurable (innerParticleWeight_measurable h y)) hb s
  rw [sourceField,sourcePotential_actualInnerSource_raw hpsi hd hy]
  unfold rawFormPair closedRawInnerField
  simp_rw [sub_mul,integral_sub (((hpsi.1 _).norm.integrable_sq).const_mul _) (hi _),integral_const_mul]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum]
  change Z/‖y‖*formMass psi-rawFormPair psi (rawWeightedCount (innerParticleWeight h y)) = _
  field_simp
  rfl

lemma rawInnerField_le_closed {N : ℕ} {h H : ℝ} (hh : h < H) (Z : ℝ)
    (x : Configuration N) (y : Space) : rawInnerField Z H x y ≤ closedRawInnerField Z h x y := by
  unfold rawInnerField closedRawInnerField rawWeightedCount
  apply sub_le_sub_left
  apply Finset.sum_le_sum
  intro i _
  unfold innerParticleWeight
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact False.elim (h2 (lt_of_le_of_lt h1 hh))
  · positivity
  · exact le_rfl

lemma rawWeightedCount_reindex {M N : ℕ} (f : Space → ℝ) (e : Fin M ≃ Fin N) (x : Configuration M) :
    rawWeightedCount f (x ∘ e.symm) = rawWeightedCount f x :=
  Equiv.sum_comp e.symm (fun i => f (x i))

lemma closedRawInnerField_reindex {M N : ℕ} (Z h : ℝ) (e : Fin M ≃ Fin N)
    (x : Configuration M) (y : Space) : closedRawInnerField Z h (x ∘ e.symm) y = closedRawInnerField Z h x y := by
  unfold closedRawInnerField; rw [rawWeightedCount_reindex]
lemma rawWeightedCount_join {N M : ℕ} (f : Space → ℝ) (x : Configuration N) (v : Configuration M) :
    rawWeightedCount f (joinLists x v) = rawWeightedCount f x+rawWeightedCount f v := by
  unfold rawWeightedCount
  rw [←Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
  simp only [joinLists_left,joinLists_right]

lemma closedRawInnerField_join {N M : ℕ} (Z h : ℝ) (x : Configuration N) (v : Configuration M)
    (hv : ∀ i, h < ‖v i‖) (y : Space) :
    closedRawInnerField Z h (joinLists x v) y = closedRawInnerField Z h x y := by
  unfold closedRawInnerField
  rw [rawWeightedCount_join]
  have hz : rawWeightedCount (innerParticleWeight h y) v = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (not_le.mpr (hv i))
  rw [hz,add_zero]
end CoulombAtom

end

end OAI
