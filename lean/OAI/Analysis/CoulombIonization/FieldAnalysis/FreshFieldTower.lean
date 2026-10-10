import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.FineSmearingPotential
import OAI.Analysis.CoulombIonization.Localization.PatchCenterObservable
import OAI.Analysis.CoulombIonization.Variational.DeletedPotential
import OAI.Analysis.CoulombIonization.Fermionic.CorePotentialTower

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_FreshFieldTower_scope

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom

lemma normalizedCoreField_weighted_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) :
    Integrable (fun u => normalizedCoreField Z lam (coreSlice ψ t u) y*formMass (coreSlice ψ t u)) := by
  have hi := ((hψ.coreSlice_mass_integrable t).const_mul (Z/‖y‖-lam)).sub
    (coreSlice_coreCoulombAt_integrable hψ t y)
  apply hi.congr
  filter_upwards [hψ.ae_coreSlice t] with u hu
  rw [normalizedCoreField_mul_mass hu]
  simp only [Pi.sub_apply]
  ring

lemma normalized_core_outer_field_tower {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (y : Space) :
    (∑ t : Spins M, ∫ u : Configuration M,
      (normalizedCoreField Z lam (coreSlice ψ t u) y-rawPotential y u)*formMass (coreSlice ψ t u)) =
      (Z/‖y‖-lam)*formMass ψ-coreCoulombAt ψ y := by
  have he (t : Spins M) :
      (fun u => (normalizedCoreField Z lam (coreSlice ψ t u) y-rawPotential y u)*formMass (coreSlice ψ t u)) =ᵐ[volume]
      fun u => (Z/‖y‖-lam)*formMass (coreSlice ψ t u)-
        (coreCoulombAt (coreSlice ψ t u) y+rawPotential y u*formMass (coreSlice ψ t u)) := by
    filter_upwards [hψ.ae_coreSlice t] with u hu
    rw [sub_mul,normalizedCoreField_mul_mass hu]
    ring
  have hint (t : Spins M) :
      (∫ u : Configuration M, (normalizedCoreField Z lam (coreSlice ψ t u) y-rawPotential y u)*
        formMass (coreSlice ψ t u)) =
      (Z/‖y‖-lam)*(∫ u, formMass (coreSlice ψ t u))-
        ∫ u, coreCoulombAt (coreSlice ψ t u) y+rawPotential y u*formMass (coreSlice ψ t u) := by
    rw [integral_congr_ae (he t)]
    have hh := integral_sub
      ((hψ.coreSlice_mass_integrable t).const_mul (Z/‖y‖-lam))
      ((coreSlice_coreCoulombAt_integrable hψ t y).add (rawPotential_coreSlice_integrable hψ t y))
    simp only [Pi.add_apply] at hh
    rw [hh,integral_const_mul]
  simp_rw [hint]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,hψ.integral_coreSlice_mass,
    fresh_core_outer_potential_tower hψ y]

lemma fresh_cut_coreCoulombAt_sum {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {ψ : FormVector N} (hψ : SobolevVector ψ) (y : Space) :
    (∑ c : Fin N → Fin 2, coreCoulombAt (orderedCutForm p hp ψ c) y) = coreCoulombAt ψ y := by
  have he (c : Fin N → Fin 2) : coreCoulombAt (orderedCutForm p hp ψ c) y =
      coreCoulombAt (multiplyForm (spatialProduct p hp c) ψ) y := by
    rw [coreCoulombAt_eq_formOneBody,orderedCutForm,formOneBody_reindex,
      ←coreCoulombAt_eq_formOneBody]
  simp_rw [he,coreCoulombAt]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [←integral_finsetSum _ (fun c _ => (hψ.multiply (spatialProduct p hp c)).shifted_nuclear_integrable s i y)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [←Finset.sum_div,finite_partition_value (spatialProduct p hp) (spatial_square_partition p hp)]

theorem fresh_cut_field_tower {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {ψ : FormVector N} (hψ : SobolevVector ψ) (Z lam : ℝ) (y : Space) :
    (∑ c : Fin N → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
      (normalizedCoreField Z lam (coreSlice (orderedCutForm p hp ψ c) t u) y-rawPotential y u)*
        formMass (coreSlice (orderedCutForm p hp ψ c) t u)) =
      (Z/‖y‖-lam)*formMass ψ-(∫ x, rawPotential y x ∂formRawLaw ψ) := by
  simp_rw [normalized_core_outer_field_tower (orderedCutForm_sobolev p hp hψ _) Z lam y]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,orderedCutForm_mass_sum p hp hψ,
    fresh_cut_coreCoulombAt_sum p hp hψ y,integral_rawPotential_formRawLaw hψ y]

end CoulombAtom

end Work_FreshFieldTower_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma retainedPatchLp_potential {N : ℕ} {b R : ℝ} (hb : 0 < b)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R) :
    tfBallPotential R (retainedPatchLp hb S x y R) 0 = tfPotential (retainedSmear b S x) y := by
  rw [←tfPotential_extension]
  have he : tfPotential (tfExtension R (retainedPatchLp hb S x y R)) 0 =
      ∫ z, retainedSmear b S x (y+z)/‖z‖ := by
    apply integral_congr_ae
    filter_upwards [retainedPatchLp_extension hb S x y hmargin] with z hz
    simp only [hz,zero_sub,norm_neg]
  rw [he]
  have ht := integral_add_left_eq_self (μ := volume)
    (fun z => retainedSmear b S x z/‖y-z‖) y
  simpa only [sub_add_cancel_left,norm_neg,tfPotential] using ht

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann CoulombAnalysis
local instance radialFineMeasurableSpace (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance radialFineBorelSpace (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma rawLocalPotential_indicator {N : ℕ} (y : Space) (q : ℝ) (x : Configuration N) :
    rawLocalPotential y q x = ∑ i, (ball y q).indicator (fun z => 1/‖y-z‖) (x i) := by
  classical
  simp only [rawLocalPotential, indicator_apply, mem_ball, dist_eq_norm, norm_sub_rev]

lemma rawPotential_retained_deleted {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) :
    rawPotential y u = rawLocalPotential y (t-7*b) u+outerDeletedPotential y t b u := by
  rw [rawPotential,rawLocalPotential,outerDeletedPotential,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ‖u i-y‖ < t-7*b
  · simp [h, not_le.mpr h]
  · simp [h, le_of_not_gt h]

lemma radial_fine_potential_loss_ae {N : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :
    ∀ᵐ u : Configuration (cutOutNumber c),
      0 ≤ rawLocalPotential y (t-7*b) u-
        tfBallPotential (t-4*b) (retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b)) 0 ∧
      rawLocalPotential y (t-7*b) u-
        tfBallPotential (t-4*b) (retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b)) 0 ≤
      rawLocalPotential y (Real.sqrt 3*b) u := by
  have he : ∀ᵐ u : Configuration (cutOutNumber c), ∀ i, u i ≠ y :=
    ae_all_iff.mpr (fun i => Measure.ae_eval_ne (fun _ : Fin (cutOutNumber c) => (volume : Measure Space)) i y)
  filter_upwards [he] with u hu
  rw [retainedPatchLp_potential hb _ u y (radialPatch_retained_margin y hb c s u)]
  have hh := retainedSmear_potential_loss hb (radialPatchRetention N y t b c s u) u y (fun i _ => hu i)
  have hret : (∑ i ∈ radialPatchRetention N y t b c s u, 1/‖y-u i‖) = rawLocalPotential y (t-7*b) u := by
    simp only [radialPatchRetention,Finset.sum_filter,rawLocalPotential,norm_sub_rev]
  rw [hret] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [rawLocalPotential_indicator]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => indicator_nonneg (fun z _ => by positivity) _)

lemma radial_fine_potential_measurable {N : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :
    Measurable (fun u : Configuration (cutOutNumber c) =>
      tfBallPotential (t-4*b) (retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b)) 0) :=
  (tfBallPotential_zero_continuous (t-4*b)).measurable.comp
    (retainedPatchLp_measurable hb (radialPatchRetention N y t b c s) id
      (radialPatchRetention_measurable N y t b c s) measurable_id y (t-4*b))

lemma radial_fine_potential_weighted_integrable {N : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
    {ψ : FormVector (cutCoreNumber c+cutOutNumber c)} (hψ : SobolevVector ψ) :
    Integrable (fun u =>
      tfBallPotential (t-4*b) (retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b)) 0*
        formMass (coreSlice ψ s u)) := by
  apply (rawLocalPotential_core_integrable hψ s y (t-7*b)).mono'
    ((radial_fine_potential_measurable y hb c s).aestronglyMeasurable.mul
      (hψ.coreSlice_mass_integrable s).aestronglyMeasurable)
  filter_upwards [radial_fine_potential_loss_ae y (t := t) hb c s] with u hu
  change ‖tfBallPotential (t-4*b) (retainedPatchLp hb _ u y (t-4*b)) 0*formMass (coreSlice ψ s u)‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg
    (tfBallPotential_nonneg (retainedPatchLp_nonneg hb _ u y _) 0) (formMass_nonneg _))]
  exact mul_le_mul_of_nonneg_right (sub_nonneg.mp hu.1) (formMass_nonneg _)

lemma radial_fine_potential_loss_integral {N : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
    {ψ : FormVector (cutCoreNumber c+cutOutNumber c)} (hψ : SobolevVector ψ) :
    0 ≤ (∫ u, rawLocalPotential y (t-7*b) u*formMass (coreSlice ψ s u))-
      (∫ u, tfBallPotential (t-4*b) (retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b)) 0*
        formMass (coreSlice ψ s u)) ∧
    (∫ u, rawLocalPotential y (t-7*b) u*formMass (coreSlice ψ s u))-
      (∫ u, tfBallPotential (t-4*b) (retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b)) 0*
        formMass (coreSlice ψ s u)) ≤
      ∫ u, rawLocalPotential y (Real.sqrt 3*b) u*formMass (coreSlice ψ s u) := by
  rw [←integral_sub (rawLocalPotential_core_integrable hψ s y _)
    (radial_fine_potential_weighted_integrable y hb c s hψ)]
  refine ⟨integral_nonneg_of_ae ?_,integral_mono_ae
    ((rawLocalPotential_core_integrable hψ s y _).sub
      (radial_fine_potential_weighted_integrable y hb c s hψ))
    (rawLocalPotential_core_integrable hψ s y _) ?_⟩
  · filter_upwards [radial_fine_potential_loss_ae y (t := t) hb c s] with u hu
    rw [←sub_mul]
    exact mul_nonneg hu.1 (formMass_nonneg _)
  · filter_upwards [radial_fine_potential_loss_ae y (t := t) hb c s] with u hu
    rw [←sub_mul]
    exact mul_le_mul_of_nonneg_right hu.2 (formMass_nonneg _)

end CoulombAtom

end

end OAI
