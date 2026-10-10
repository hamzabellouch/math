import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.CorePotentialTower
import OAI.Analysis.CoulombIonization.Localization.OrdinaryDensity
import OAI.Analysis.CoulombIonization.FieldAnalysis.InnerExterior

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
noncomputable section
namespace CoulombAtom

 def actualParticleSource {N : ℕ} (psi : FormVector N) : Measure Space :=
   ENNReal.ofReal ((formMass psi)⁻¹) • rawOneParticleLaw (formRawLaw psi)

 def actualInnerSource {N : ℕ} (psi : FormVector N) (h : ℝ) : Measure Space :=
   (actualParticleSource psi).restrict {a | ‖a‖ ≤ h}

 lemma actualParticleSource_finite {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) : IsFiniteMeasure (actualParticleSource psi) := by
   let : IsFiniteMeasure (formRawLaw psi) := formRawLaw_finite hpsi
   let : IsFiniteMeasure (rawOneParticleLaw (formRawLaw psi)) := rawOneParticleLaw_finite _
   refine ⟨?_⟩
   change (ENNReal.ofReal ((formMass psi)⁻¹) • rawOneParticleLaw (formRawLaw psi)) Set.univ < ⊤
   rw [Measure.smul_apply]
   exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

 lemma actualInnerSource_finite {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (h : ℝ) : IsFiniteMeasure (actualInnerSource psi h) := by
   let : IsFiniteMeasure (actualParticleSource psi) := actualParticleSource_finite hpsi
   unfold actualInnerSource
   infer_instance

 lemma actualInnerSource_support {N : ℕ} (psi : FormVector N) (h : ℝ) :
     ∀ᵐ a ∂actualInnerSource psi h, ‖a‖ ≤ h :=
   ae_restrict_mem (measurableSet_le continuous_norm.measurable measurable_const)

 lemma rawOneParticleLaw_potential_integrable {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (y : Space) :
     Integrable (fun a => ‖y-a‖⁻¹) (rawOneParticleLaw (formRawLaw psi)) := by
   have hm : Measurable (fun a : Space => ‖y-a‖⁻¹) :=
     ((continuous_const.sub continuous_id).norm.measurable).inv
   rw [rawOneParticleLaw,Measure.sum_fintype,integrable_finsetSum_measure]
   intro i _
   apply (integrable_map_measure hm.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).mpr
   apply (rawPotential_form_integrable hpsi y).mono'
     ((hm.comp (measurable_pi_apply i)).aestronglyMeasurable)
   apply ae_of_all
   intro x
   simp only [Function.comp_apply,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
   rw [norm_sub_rev]
   simpa only [one_div,rawPotential] using Finset.single_le_sum (f := fun j : Fin N => 1/‖x j-y‖)
     (fun _ _ => by positivity) (Finset.mem_univ i)

 lemma sourcePotential_rawOneParticleLaw {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (y : Space) :
     sourcePotential (rawOneParticleLaw (formRawLaw psi)) y = coreCoulombAt psi y := by
   have hm : Measurable (fun a : Space => ‖y-a‖⁻¹) :=
     ((continuous_const.sub continuous_id).norm.measurable).inv
   have hi := rawOneParticleLaw_potential_integrable hpsi y
   rw [rawOneParticleLaw,Measure.sum_fintype,integrable_finsetSum_measure] at hi
   have hp := rawOneParticleLaw_pairing (formRawLaw psi) hm (fun i =>
     (integrable_map_measure hm.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).mp
       (hi i (Finset.mem_univ i)))
   unfold sourcePotential
   rw [hp]
   convert integral_rawPotential_formRawLaw hpsi y using 1
   apply integral_congr_ae
   apply ae_of_all
   intro x
   apply Finset.sum_congr rfl
   intro i _
   simp only [one_div,norm_sub_rev]

 lemma actualParticleSource_potential_integrable {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (y : Space) :
     Integrable (fun a => ‖y-a‖⁻¹) (actualParticleSource psi) :=
   (rawOneParticleLaw_potential_integrable hpsi y).smul_measure ENNReal.ofReal_ne_top

 lemma sourcePotential_actualParticleSource {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (y : Space) :
     sourcePotential (actualParticleSource psi) y = coreCoulombAt psi y/formMass psi := by
   simp only [sourcePotential,actualParticleSource,integral_smul_measure,
     ENNReal.toReal_ofReal (inv_nonneg.mpr (formMass_nonneg psi)),smul_eq_mul]
   change (formMass psi)⁻¹*sourcePotential (rawOneParticleLaw (formRawLaw psi)) y = _
   rw [sourcePotential_rawOneParticleLaw hpsi]
   ring

 lemma sourceField_actualParticleSource {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (hm : formMass psi ≠ 0) (Z lam : ℝ) (y : Space) :
     sourceField Z (actualParticleSource psi) y = normalizedCoreField Z lam psi y+lam := by
   rw [sourceField,sourcePotential_actualParticleSource hpsi]
   unfold normalizedCoreField
   field_simp [hm]
   ring

 lemma sourcePotential_inner_add_outer {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (h : ℝ) (y : Space) :
     sourcePotential (actualInnerSource psi h) y+
         sourcePotential ((actualParticleSource psi).restrict {a | h < ‖a‖}) y =
       sourcePotential (actualParticleSource psi) y := by
   have hc : {a : Space | h < ‖a‖} = {a : Space | ‖a‖ ≤ h}ᶜ := by
     ext a; simp only [mem_ofPred_eq,mem_compl_iff,not_le]
   rw [hc]
   exact integral_add_compl (measurableSet_le continuous_norm.measurable measurable_const)
     (actualParticleSource_potential_integrable hpsi y)

 lemma sourceField_inner_eq {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (hm : formMass psi ≠ 0) (Z lam h : ℝ) (y : Space) :
     sourceField Z (actualInnerSource psi h) y = normalizedCoreField Z lam psi y+lam+
         sourcePotential ((actualParticleSource psi).restrict {a | h < ‖a‖}) y := by
   have hp := sourcePotential_inner_add_outer hpsi h y
   have hf := sourceField_actualParticleSource hpsi hm Z lam y
   unfold sourceField at hf ⊢
   linarith only [hp,hf]

 lemma sourceField_inner_harmonic {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (Z : ℝ) {h : ℝ} (hh : 0 ≤ h)
     {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
     (hsg : tsupport g ⊆ {y | h < ‖y‖}) :
     (∫ y, sourceField Z (actualInnerSource psi h) y*Δ g y) = 0 := by
   let : IsFiniteMeasure (actualInnerSource psi h) := actualInnerSource_finite hpsi h
   exact sourceField_weak_harmonic Z _ hh (actualInnerSource_support psi h) hg hcg hsg

end CoulombAtom

end

end OAI
