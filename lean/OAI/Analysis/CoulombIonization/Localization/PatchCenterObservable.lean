import Mathlib
import OAI.Analysis.CoulombIonization.Variational.IntegratedTruncatedControl
import OAI.Analysis.CoulombIonization.ThomasFermi.TFMeanComparison

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann
local instance patchCenterMeasurableSpace (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance patchCenterBorelSpace (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

def conditionalPatchCenter {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) (u : Configuration M) : ℝ :=
  normalizedCoreField Z lam (coreSlice ψ t u) y-
    tfBallPotential R (tfPatchMinimizer R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u)) 0

def weightedNegativePatchCenter {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) (u : Configuration M) : ℝ :=
  formMass (coreSlice ψ t u)*max (-conditionalPatchCenter ψ t Z lam y R u) 0

lemma weightedNegativePatchCenter_nonneg {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) (u : Configuration M) :
    0 ≤ weightedNegativePatchCenter ψ t Z lam y R u :=
  mul_nonneg (formMass_nonneg _) (le_max_right _ _)

lemma normalizedCoreField_eval_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) :
    AEMeasurable (fun u => normalizedCoreField Z lam (coreSlice ψ t u) y) := by
  obtain ⟨F,hF,he⟩ := coreSlice_field_measurable_rep hψ t Z lam
  exact ((hF.comp (measurable_id.prodMk measurable_const)).aemeasurable).congr
    (he.mono fun u hu => hu y)

lemma tfBallPotential_zero_continuous (R : ℝ) :
    Continuous (fun f : TFLp (ballMeasure R) => tfBallPotential R f 0) := by
  convert patch_test_continuous_of_memLp R (nuclear_memLp R) using 1
  funext f
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [zero_sub,norm_neg]
    ring

lemma conditionalPatchCenter_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ) :
    AEMeasurable (conditionalPatchCenter ψ t Z lam y R) :=
  (normalizedCoreField_eval_aemeasurable hψ t Z lam y).sub
    ((tfBallPotential_zero_continuous R).measurable.comp_aemeasurable
      (conditionalPatchMinimizer_aemeasurable hψ t Z lam y R))

lemma weightedNegativePatchCenter_aestronglyMeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ) :
    AEStronglyMeasurable (weightedNegativePatchCenter ψ t Z lam y R) := by
  exact (hψ.coreSlice_mass_integrable t).aestronglyMeasurable.mul
    (((conditionalPatchCenter_aemeasurable hψ t Z lam y R).neg.max
      aemeasurable_const).aestronglyMeasurable)

theorem negativePatchCenter_integral_event {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (Z lam : ℝ) {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hi : Integrable (weightedPatchGap ψ t Z lam y R hb S))
    {q m : ℝ} (hq : 0 < q) (hqR : q ≤ R/12)
    (hsmall : tfPatchOscillationConstant/R*q ≤ 1/2) (hm : 0 < m)
    (B : Set (Configuration M)) (hB : MeasurableSet B)
    (hcount : ∀ᵐ u ∂volume.restrict B,
      m ≤ ∫ z in ball (0 : Space) q, retainedPatchLp hb (S u) u y R z ∂ballMeasure R) :
    (∫ u in B, weightedNegativePatchCenter ψ t Z lam y R u) ≤
      (2/m)*(∫ u, weightedPatchGap ψ t Z lam y R hb S u)+
      (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4)*(∫ u in B, formMass (coreSlice ψ t u)) := by
  have hbound : ∀ᵐ u ∂volume.restrict B,
      weightedNegativePatchCenter ψ t Z lam y R u ≤
        (2/m)*weightedPatchGap ψ t Z lam y R hb S u+
        (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4)*formMass (coreSlice ψ t u) := by
    have hc0 := (ae_restrict_iff' hB).mp hcount
    filter_upwards [ae_restrict_of_ae (hψ.ae_coreSlice t),
      ae_restrict_of_ae hc0, ae_restrict_mem hB] with u hu hc hmem
    have hh := conditionalRetained_negative_center ψ t u hu A (hcore u) y hR hd hr hnuc hsep Z lam
      hb S hq hqR hsmall hm (hc hmem)
    simpa only [weightedNegativePatchCenter,conditionalPatchCenter,add_zero] using hh
  have hmassi : IntegrableOn (fun u => formMass (coreSlice ψ t u)) B :=
    (hψ.coreSlice_mass_integrable t).integrableOn
  have hgi := (hi.integrableOn (s := B)).const_mul (2/m)
  have hci := hmassi.const_mul (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4)
  have hf : IntegrableOn (weightedNegativePatchCenter ψ t Z lam y R) B :=
    (hgi.add hci).mono'
      ((weightedNegativePatchCenter_aestronglyMeasurable hψ t Z lam y R).mono_measure Measure.restrict_le_self)
      (hbound.mono fun u hu => by
        rw [Real.norm_of_nonneg (weightedNegativePatchCenter_nonneg ψ t Z lam y R u)]
        exact hu)
  have he := integral_mono_ae hf (hgi.add hci) hbound
  simp only [Pi.add_apply] at he
  rw [integral_add hgi hci,integral_const_mul,integral_const_mul] at he
  apply he.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2/m)
  exact setIntegral_le_integral hi (Eventually.of_forall fun u => weightedPatchGap_nonneg ψ t Z lam y R hb S u)

end CoulombAtom

end

end OAI
