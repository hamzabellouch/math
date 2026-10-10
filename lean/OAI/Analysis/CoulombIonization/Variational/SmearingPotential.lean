import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CompactPotential

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

def spatialSmearing (η ρ : Space → ℝ) (x : Space) : ℝ := ∫ z : Space, ρ z*η (x-z)

lemma integral_translated_pole (η : Space → ℝ) (a z : Space) :
    (∫ x : Space, η (x-z)/‖a-x‖) = CoulombAnalysis.tfPotential η (a-z) := by
  calc
    _ = ∫ x : Space, η (x-z)/‖(a-z)-(x-z)‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show (a-z)-(x-z)=a-x by abel]
    _ = _ := integral_sub_right_eq_self (fun y : Space => η y/‖(a-z)-y‖) z

lemma translated_pole_integrable {η : Space → ℝ} (h1 : Integrable η)
    (hp : MemLp η (5/3 : ENNReal)) (a z : Space) :
    Integrable (fun x : Space => η (x-z)/‖a-x‖) := by
  have hi := (CoulombAnalysis.tfPotential_integrable h1 hp (a-z)).comp_sub_right z
  apply hi.congr
  filter_upwards [] with x
  rw [show (a-z)-(x-z)=a-x by abel]

lemma smearing_pole_integrable {η ρ : Space → ℝ} (hη : Continuous η)
    (hcη : HasCompactSupport η) (hmρ : Measurable ρ) (hρ : Integrable ρ) (a : Space) :
    Integrable (fun r : Space × Space => ρ r.1*η (r.2-r.1)/‖a-r.2‖) := by
  have h1 : Integrable η := hη.integrable_of_hasCompactSupport hcη
  have hp : MemLp η (5/3 : ENNReal) := hη.memLp_of_hasCompactSupport hcη
  have hm : Measurable (fun r : Space × Space => ρ r.1*η (r.2-r.1)/‖a-r.2‖) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  refine ⟨Eventually.of_forall (fun z => ?_),?_⟩
  · simpa only [mul_div_assoc] using (translated_pole_integrable h1 hp a z).const_mul (ρ z)
  · obtain ⟨C,hC⟩ := compact_potential_bounded hη.norm hcη.norm
    have hi : Integrable (fun z => ‖ρ z‖*CoulombAnalysis.tfPotential (fun x => ‖η x‖) (a-z)) := by
      apply (hρ.norm.mul_const C).mono'
        ((hmρ.norm.mul ((CoulombAnalysis.tfPotential_continuous h1.norm hp.norm).measurable.comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable)
      filter_upwards [] with z
      change ‖‖ρ z‖*CoulombAnalysis.tfPotential (fun x => ‖η x‖) (a-z)‖ ≤ ‖ρ z‖*C
      rw [norm_mul,norm_norm,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC (a-z)) (abs_nonneg _)
    apply hi.congr
    filter_upwards [] with z
    simp only [norm_div,norm_mul,norm_norm,mul_div_assoc,integral_const_mul]
    rw [integral_translated_pole (fun x => ‖η x‖) a z]

lemma spatialSmearing_potential {η ρ : Space → ℝ} (hη : Continuous η)
    (hcη : HasCompactSupport η) (hmρ : Measurable ρ) (hρ : Integrable ρ) (a : Space) :
    CoulombAnalysis.tfPotential (spatialSmearing η ρ) a =
      ∫ z : Space, ρ z*CoulombAnalysis.tfPotential η (a-z) := by
  have hi := smearing_pole_integrable hη hcη hmρ hρ a
  change (∫ x : Space, (∫ z : Space, ρ z*η (x-z))/‖a-x‖) = _
  calc
    _ = ∫ x : Space, ∫ z : Space, ρ z*η (x-z)/‖a-x‖ := by simp only [integral_div]
    _ = ∫ z : Space, ∫ x : Space, ρ z*η (x-z)/‖a-x‖ := integral_integral_swap hi.swap
    _ = _ := by simp only [mul_div_assoc,integral_const_mul,integral_translated_pole]

lemma smearing_potential_integrable {η ρ : Space → ℝ} (hη : Continuous η)
    (hcη : HasCompactSupport η) (hmρ : Measurable ρ) (hρ : Integrable ρ) (a : Space) :
    Integrable (fun z : Space => ρ z*CoulombAnalysis.tfPotential η (a-z)) := by
  have hi := (smearing_pole_integrable hη hcη hmρ hρ a).integral_prod_left
  simpa only [mul_div_assoc,integral_const_mul,integral_translated_pole] using hi

end CoulombAtom

end

end OAI
