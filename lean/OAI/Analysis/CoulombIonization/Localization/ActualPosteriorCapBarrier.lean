import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.BarrierInitialEventBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.ExpectedRadialCapBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.SharpBudgetMonotoneBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma jointMasterPosterior_potential_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun z : OriginalDatum N K ell j =>
      tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g z) y) := by
  have hm : Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2 / ‖y-p.2‖) :=
    (jointMasterPosterior_measurable μ ell j hc hr hs hg).div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma normalized_setIntegral_const_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : Set Ω) {f : Ω → ℝ}
    (hi : Integrable f μ) (hp : 0 < (μ A).toReal) (c : ℝ) :
    ((μ A).toReal)⁻¹*(∫ x in A, c-f x ∂μ) =
      c-((μ A).toReal)⁻¹*(∫ x in A, f x ∂μ) := by
  rw [integral_sub (integrable_const c) hi.integrableOn,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_sub,←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]

def dyadicUniformEventBudget (r p₀ δ : ℝ) : ℝ :=
  observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/p₀))^5+δ

lemma dyadicUniformEventBudget_nonneg {r p₀ δ : ℝ}
    (hr : 0 < r) (hp : 0 < p₀) (hp1 : p₀ ≤ 1) (hδ : 0 ≤ δ) :
    0 ≤ dyadicUniformEventBudget r p₀ δ := by
  have hlog : 0 ≤ Real.log (Real.exp 1/p₀) := by
    rw [eventLog_eq hp]
    linarith [Real.log_nonpos hp.le hp1]
  unfold dyadicUniformEventBudget
  exact add_nonneg (mul_nonneg (mul_nonneg observationFisherConstant_pos.le
    (Real.rpow_nonneg hr.le _)) (pow_nonneg hlog _)) hδ

lemma dyadicUniformEventBudget_mono {r p₀ p δ : ℝ}
    (hr : 0 < r) (h₀ : 0 < p₀) (hp : p₀ ≤ p) (hp1 : p ≤ 1) :
    observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/p))^5+δ ≤
      dyadicUniformEventBudget r p₀ δ := by
  have hp' : 0 < p := h₀.trans_le hp
  have hlog : 0 ≤ Real.log (Real.exp 1/p) := by
    rw [eventLog_eq hp']
    linarith [Real.log_nonpos hp'.le hp1]
  have hh : Real.log (Real.exp 1/p) ≤ Real.log (Real.exp 1/p₀) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_left (Real.exp_pos 1).le h₀ hp
  unfold dyadicUniformEventBudget
  exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog hh 5)
    (mul_nonneg observationFisherConstant_pos.le (Real.rpow_nonneg hr.le _))) le_rfl

theorem actual_posterior_pointwise_cap {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) (hr : 0 < r) {N : ℕ} (hN : PriceMinimizes (energy Z) lam N)
    (K j : ℕ) {p₀ δ : ℝ} (h₀ : 0 < p₀) (h₀1 : p₀ ≤ 1) (hδ : 0 < δ)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (y : Space) (_hy : y ≠ 0) (_ha1 : localCellRadius y ≤ 1)
        (_hry : r₀ ≤ ‖y‖) (b q θ : ℝ) (_hb : 0 < b) (_hba : 2*b ≤ localCellRadius y)
        (_hq : 0 < q) (_hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
        (_hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
        (_hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3)),
      tfPatchCapConstant/(localCellRadius y)^4+
        (sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (dyadicUniformEventBudget r p₀ δ) y)
          (dyadicUniformEventBudget r p₀ δ) q+
        sharpLocalPotentialBudget (localCellRadius y)
          (localOffsetMass (dyadicUniformEventBudget r p₀ δ) y)
          (2*masterWidth c₁ r₀ s y)) < θ →
      ((physicalObservationLaw (graphRawLaw F) K)
        {z | θ < Z/‖y‖-lam-tfPotential (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
            (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z)) y}).toReal < p₀ := by
  obtain ⟨F,hFn,hFE,hTilt⟩ := quantum_uniform_near_minimizer_dyadic_event_tilt hZ hr N K h₀ hδ
  refine ⟨F,hFn,hFE,?_⟩
  intro y hy ha1 hry b q θ hb hba hq hqr hqR hcollar hsmall
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let P := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
      (originalDatum ell j z)) y
  let A := {z | θ < Z/‖y‖-lam-P z}
  have hA : MeasurableSet[observationInformation ell j] A :=
    measurableSet_lt measurable_const (measurable_const.sub
      (jointMasterPosterior_potential_measurable (graphRawLaw F) ell j y hc hr₀ hs canonicalRealPacket_smooth.continuous))
  obtain ⟨B,hB,hsy,hBA⟩ := observation_event_symmetric_representation ell j hA
  let p := ((physicalObservationLaw (graphRawLaw F) K) A).toReal
  have hpB : physicalObservationProbability F ell B = p := by
    change ((physicalObservationLaw (graphRawLaw F) K) (physicalObservationEvent ell B)).toReal = p
    rw [hBA]
  change p < p₀
  by_contra! hn
  have hp : 0 < p := h₀.trans_le hn
  obtain ⟨G,hGn,hlaw,hGE⟩ := hTilt B hB hsy (by change p₀ ≤ physicalObservationProbability F ell B; rwa [hpB])
  have hple : p ≤ 1 := hpB ▸ physicalObservationProbability_le_one F hFn ell B
  have hDE : max (corePriceExcess Z lam (graphFormVector G)) 0 ≤ dyadicUniformEventBudget r p₀ δ := by
    apply max_le _ (dyadicUniformEventBudget_nonneg hr h₀ h₀1 hδ.le)
    apply (priced_graph_tilt_excess hN G hGn (by simpa only [add_assoc] using hGE)).trans
    change observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/physicalObservationProbability F ell B))^5+δ ≤ _
    rw [hpB]
    exact dyadicUniformEventBudget_mono hr h₀ hn hple
  have hcollar' : localCellRadius y ≤ b^2*localOffsetMass
      (max (corePriceExcess Z lam (graphFormVector G)) 0) y := by
    apply hcollar.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
    unfold localOffsetMass
    linarith [le_max_left (1/(localCellRadius y)^3) 1,Real.sqrt_nonneg
      (max (corePriceExcess Z lam (graphFormVector G)) 0*localCellRadius y)]
  have hupper := sharp_eventLaw_field_cap hZ hlam F G hGn ell j
    (by rwa [hBA]) (by rwa [hpB]) hlaw hy ha1 hc hcL hr₀ hs hs1 hry hb hba hq hqr hqR hcollar'
  have herror := sharp_combined_error_mono hy hb hq hDE
    (by linarith [masterWidth_pos hc hr₀ hs y] : 0 ≤ 2*masterWidth c₁ r₀ s y)
  rw [hpB,hBA] at hupper
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  have hPi : Integrable P (physicalObservationLaw (graphRawLaw F) K) :=
    jointMasterPosterior_potential_integrable (graphRawLaw F) ell j y hi he hc hr₀ hs
      canonicalRealPacket_smooth canonicalRealPacket_compact canonicalRealPacket_normalized
        canonicalRealPacket_radial canonicalRealPacket_support
  have hlower := threshold_event_mean_ge (physicalObservationLaw (graphRawLaw F) K)
    ((integrable_const (Z/‖y‖-lam)).sub hPi) ((observationInformation_le ell j) A hA)
    (fun z hz => hz.le) hp
  simp only [Pi.sub_apply] at hlower
  rw [normalized_setIntegral_const_sub _ A hPi hp] at hlower
  exact (not_le_of_gt (lt_of_le_of_lt (hupper.trans (add_le_add le_rfl herror)) hsmall)) hlower

end CoulombAtom

end

end OAI
