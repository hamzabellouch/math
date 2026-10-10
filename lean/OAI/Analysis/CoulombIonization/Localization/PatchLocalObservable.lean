import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchTruncationLoss

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAnalysis
open CoulombAtom

lemma local_coulomb_pair_eq {R q : ℝ} (hqR : q ≤ R)
    (f : TFLp (ballMeasure R)) (hf : NonnegDensity f) :
    (∫ x, ((ball (0 : Space) q).indicator (fun z => 1/‖z‖) x)*f x ∂ballMeasure R) =
      ∫ x in ball 0 q, ‖f x‖/‖x‖ := by
  have hh : (fun x => ((ball (0 : Space) q).indicator (fun z => 1/‖z‖) x)*f x) =
      (ball (0 : Space) q).indicator (fun x => f x/‖x‖) := by
    funext x
    by_cases hx : x ∈ ball (0 : Space) q
    · simp only [indicator_of_mem hx]; ring
    · simp only [indicator_of_notMem hx,zero_mul]
  rw [hh,integral_indicator measurableSet_ball]
  change (∫ x, f x/‖x‖ ∂(volume.restrict (ball 0 R)).restrict (ball 0 q)) = _
  rw [Measure.restrict_restrict measurableSet_ball,inter_eq_left.mpr (ball_subset_ball hqR)]
  apply integral_congr_ae
  filter_upwards [ae_mono (Measure.restrict_mono (ball_subset_ball hqR) le_rfl) hf] with x hx
  rw [Real.norm_of_nonneg hx]

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis CoulombNeumann
local instance instMeasurableSpacePatchLocalObservableTFLp (R : ℝ) :
    MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance instBorelSpacePatchLocalObservableTFLp (R : ℝ) :
    BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

def weightedPatchLocalPotential {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (y : Space) (R q : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (u : Configuration M) : ℝ :=
  formMass (coreSlice ψ s u)*
    (∫ x in ball 0 q, ‖retainedPatchLp hb (S u) u y R x‖/‖x‖)

lemma retainedPatchLocalPotential_nonneg {M : ℕ} (y : Space) (R q : ℝ)
    {b : ℝ} (hb : 0 < b) (S : Finset (Fin M)) (u : Configuration M) :
    0 ≤ ∫ x in ball 0 q, ‖retainedPatchLp hb S u y R x‖/‖x‖ :=
  integral_nonneg (fun _ => div_nonneg (norm_nonneg _) (norm_nonneg _))

lemma retainedPatchLocalPotential_le {M : ℕ} (y : Space) {R q : ℝ}
    (hq : 0 < q) (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Finset (Fin M)) (u : Configuration M) :
    (∫ x in ball 0 q, ‖retainedPatchLp hb S u y R x‖/‖x‖) ≤
      2*Real.pi*(M*b⁻¹^3)*q^2 := by
  have hmeasure : ballMeasure q ≤ ballMeasure R :=
    Measure.restrict_mono (ball_subset_ball hqR) le_rfl
  apply local_coulomb_le_of_density_cap hq
    ((Lp.memLp (retainedPatchLp hb S u y R)).mono_measure hmeasure)
  filter_upwards [ae_mono hmeasure (retainedPatchLp_nonneg hb S u y R),
    ae_mono hmeasure (retainedPatchLp_bound hb S u y R)] with x hx hxcap
  rw [Real.norm_of_nonneg hx]
  apply hxcap.trans
  have hcNat : S.card ≤ M := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hc : (S.card : ℝ) ≤ M := by exact_mod_cast hcNat
  exact mul_le_mul_of_nonneg_right hc (by positivity)

lemma retainedPatchLocalPotential_measurable {M : ℕ} (y : Space) {R q : ℝ}
    (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u}) :
    Measurable (fun u => ∫ x in ball 0 q, ‖retainedPatchLp hb (S u) u y R x‖/‖x‖) := by
  have hg := (nuclear_memLp R).indicator measurableSet_ball (s := ball (0 : Space) q)
  have hs := retainedPatchLp_measurable hb S id hS measurable_id y R
  have hm := (patch_test_continuous_of_memLp R hg).measurable.comp hs
  convert hm using 1
  funext u
  simpa only [one_div,Function.comp_apply,id_eq] using
    (local_coulomb_pair_eq hqR _ (retainedPatchLp_nonneg hb (S u) u y R)).symm

lemma weightedPatchLocalPotential_nonneg {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (y : Space) (R q : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (u : Configuration M) :
    0 ≤ weightedPatchLocalPotential ψ s y R q hb S u :=
  mul_nonneg (formMass_nonneg _) (retainedPatchLocalPotential_nonneg y R q hb _ u)

lemma weightedPatchLocalPotential_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) {R q : ℝ}
    (hq : 0 < q) (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u}) :
    Integrable (weightedPatchLocalPotential ψ s y R q hb S) := by
  have hm := (retainedPatchLocalPotential_measurable y hqR hb S hS).aestronglyMeasurable (μ := volume)
  have hd : ∀ᵐ u, ‖∫ x in ball 0 q, ‖retainedPatchLp hb (S u) u y R x‖/‖x‖‖ ≤
      2*Real.pi*(M*b⁻¹^3)*q^2 := by
    filter_upwards [] with u
    rw [Real.norm_of_nonneg (retainedPatchLocalPotential_nonneg y R q hb _ u)]
    exact retainedPatchLocalPotential_le y hq hqR hb _ u
  exact ((hψ.coreSlice_mass_integrable s).bdd_mul hm hd).congr
    (Eventually.of_forall fun _ => mul_comm _ _)

end CoulombAtom

end

end OAI
