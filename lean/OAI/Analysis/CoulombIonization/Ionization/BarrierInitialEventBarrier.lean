import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.ActualUnshiftedBudget
import OAI.Analysis.CoulombIonization.Localization.BarrierOrdinaryGlobalBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierTruncationBarrier
import OAI.Analysis.CoulombIonization.Localization.BarrierEventSymmetryBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis

lemma jointMasterPosterior_inner_eq_kernel {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (r : ℝ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    (fun z => innerPotential r (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y) =ᵐ[
      physicalObservationLaw μ K] fun z => kernelPosteriorTest μ ell j
        (fun x => innerPotential r (masterKernel c₁ r₀ s g x) y) (originalDatum ell j z) := by
  filter_upwards [originalRawKernel_integrable μ ell j (rawPotential_measurable y) hi,
    originalRawKernel_ae μ ell j he] with z hz hze
  exact inner_master_configuration_fubini _ r y hz hze hc hr hs hg hcg hgn hrad hgs

lemma jointMasterPosterior_inner_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (r : ℝ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun z => innerPotential r (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y)
      (physicalObservationLaw μ K) :=
  (kernelPosteriorTest_integrable μ ell j (inner_master_potential_measurable hc hr hs hg.continuous r y)
    (inner_master_configuration_integrable μ r y hi he hc hr hs hg hcg hgn hrad hgs)).congr
      (jointMasterPosterior_inner_eq_kernel μ ell j r y hi he hc hr hs hg hcg hgn hrad hgs).symm

lemma jointMasterPosterior_inner_event {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (r : ℝ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) :
    (∫ z in A, innerPotential r (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
      ∂physicalObservationLaw μ K) =
      ∫ z in A, ∑ i, innerPotential r (masterKernel c₁ r₀ s g (z.1 i)) y ∂physicalObservationLaw μ K := by
  rw [integral_congr_ae (ae_restrict_of_ae
    (jointMasterPosterior_inner_eq_kernel μ ell j r y hi he hc hr hs hg hcg hgn hrad hgs))]
  exact kernelPosteriorTest_setIntegral μ ell j (inner_master_potential_measurable hc hr hs hg.continuous r y)
    (inner_master_configuration_integrable μ r y hi he hc hr hs hg hcg hgn hrad hgs) hA

theorem normalized_inner_event_bound {N K : ℕ} (μ ν : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    (hiν : Integrable (rawPotential y) ν) (heν : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    (hy : ‖y‖ ≤ (11/10)*r₀)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) {p : ℝ} (hp : 0 < p)
    (hlaw : ν = (ENNReal.ofReal p)⁻¹ • Measure.map Prod.fst ((physicalObservationLaw μ K).restrict A)) :
    p⁻¹*(∫ z in A, innerPotential r₀ (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
      ∂physicalObservationLaw μ K) ≤ ∫ x, rawLocalPotential y (4*r₀) x ∂ν := by
  rw [jointMasterPosterior_inner_event μ ell j r₀ y hi he hc hr hs hg hcg hgn hrad hgs hA,
    ←normalized_event_integral μ ν A hp hlaw
      (f := fun x : Configuration N => ∑ i, innerPotential r₀ (masterKernel c₁ r₀ s g (x i)) y)
      (Finset.measurable_sum _ (fun i _ =>
        (inner_master_potential_measurable hc hr hs hg.continuous r₀ y).comp (measurable_pi_apply i)))]
  apply integral_mono_ae
    (inner_master_configuration_integrable ν r₀ y hiν heν hc hr hs hg hcg hgn hrad hgs)
    (rawLocalPotential_integrable_of_raw y _ hiν)
  filter_upwards [heν] with x hx
  unfold rawLocalPotential
  apply Finset.sum_le_sum
  intro i _
  exact inner_master_potential_raw_bound hc hc1 hr hs hs1 hg hcg hgn hrad hgs (hx i) hy

theorem normalized_inner_event_global_bound {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    {ψ : FormVector N} (hψ : FormAdmissible ψ)
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    (hy : ‖y‖ ≤ (11/10)*r₀)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) {p : ℝ} (hp : 0 < p)
    (hlaw : formRawLaw ψ = (ENNReal.ofReal p)⁻¹ • Measure.map Prod.fst ((physicalObservationLaw μ K).restrict A))
    {Z δ : ℝ} (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hN : (N:ℝ) ≤ 3*Z)
    (hE : formEnergy Z ψ ≤ allSectorEnergy Z+δ) :
    p⁻¹*(∫ z in A, innerPotential r₀ (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
      ∂physicalObservationLaw μ K) ≤
      (Pauli.globalDensityConstant*(Z^(7/3:ℝ)+δ))^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*(4*r₀)^(1/5:ℝ) := by
  have hsv := hψ.sobolevFermion.sobolevVector
  apply (normalized_inner_event_bound μ (formRawLaw ψ) ell j y hi he
    (rawPotential_form_integrable hsv y) (formRawLaw_ae_no_poles ψ y)
    hc hc1 hr hs hs1 hg hcg hgn hrad hgs hy hA hp hlaw).trans
  apply (ordinaryDensity_raw_local_holder hsv y (by positivity)
    ((ordinaryDensity_memLp hψ).restrict _)).trans
  have hloc : (∫ z in ball y (4*r₀), (ordinaryDensity ψ z)^(5/3:ℝ)) ≤
      Pauli.globalDensityConstant*(Z^(7/3:ℝ)+δ) := by
    apply (setIntegral_le_integral ?_ (ae_of_all _ (fun z => Real.rpow_nonneg (ordinaryDensity_nonneg ψ z) _))).trans
    · exact ordinaryDensity_global_unshifted hZ hδ hN ψ hψ hE
    · have hh := (ordinaryDensity_memLp hψ).integrable_norm_rpow (by norm_num : (5/3:ENNReal) ≠ 0)
        (ENNReal.div_ne_top (by norm_num) (by norm_num) : (5/3:ENNReal) ≠ ⊤)
      simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat,Real.norm_of_nonneg (ordinaryDensity_nonneg ψ _)] using hh
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Real.rpow_le_rpow (integral_nonneg (fun z => Real.rpow_nonneg (ordinaryDensity_nonneg ψ z) _)) hloc (by norm_num)

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma jointMasterPosterior_inner_measurable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (r : ℝ) (y : Space)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun z : OriginalDatum N K ell j =>
      innerPotential r (jointMasterPosterior μ ell j c₁ r₀ s g z) y) := by
  have hm : Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2 / ‖y-p.2‖) :=
    (jointMasterPosterior_measurable μ ell j hc hr hs hg).div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma threshold_event_mean_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hi : Integrable f μ) {t : ℝ} {A : Set Ω} (hA : MeasurableSet A)
    (hAB : ∀ z ∈ A, t ≤ f z) (hp : 0 < (μ A).toReal) :
    t ≤ ((μ A).toReal)⁻¹*(∫ z in A, f z ∂μ) := by
  have he : (μ A).toReal*t ≤ ∫ z in A, f z ∂μ := by
    calc
      _ = ∫ z in A, t ∂μ := by simp [Measure.real,smul_eq_mul]
      _ ≤ _ := setIntegral_mono_on (integrable_const _).integrableOn hi.integrableOn hA hAB
  have hm := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hp.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul] using hm

theorem actual_initial_pointwise_exceptional (Z : ℕ) (hZ : 1 ≤ Z)
    {lam r₀ s c₁ : ℝ} (hlam : 0 < lam) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2) {N : ℕ} (hN : PriceMinimizes (energy Z) lam N)
    (K j : ℕ) {p₀ δ θ : ℝ} (h₀ : 0 < p₀) (hδ : 0 < δ)
    (hbudget : 3*(Z:ℝ)*lam+observationFisherConstant*r₀^(-2.02:ℝ)*
      (Real.log (Real.exp 1/p₀))^5+δ ≤ (Z:ℝ)^(7/3:ℝ))
    (hsmall : (Pauli.globalDensityConstant*((Z:ℝ)^(7/3:ℝ)+(Z:ℝ)^(7/3:ℝ)))^(3/5:ℝ)*
      (8*Real.pi)^(2/5:ℝ)*(4*r₀)^(1/5:ℝ) < θ)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    N ≤ 3*Z ∧ ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ y : Space, ‖y‖ ≤ (11/10)*r₀ →
        ((physicalObservationLaw (graphRawLaw F) K)
          {z | θ < innerPotential r₀ (jointMasterPosterior (graphRawLaw F)
            (fun k : Fin K => dyadicObservationWidth r₀ k) j c₁ r₀ s g
              (originalDatum (fun k : Fin K => dyadicObservationWidth r₀ k) j z)) y}).toReal < p₀ := by
  obtain ⟨hcount,F,hn,hF,hTilt⟩ := actual_priced_uniform_unshifted_event_tilt Z hZ hlam hr hN K h₀ hδ
  refine ⟨hcount,F,hn,hF,?_⟩
  intro y hy
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r₀ k
  let P : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) → ℝ :=
    fun z => innerPotential r₀ (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g (originalDatum ell j z)) y
  let A := {z | θ < P z}
  have hA : MeasurableSet[observationInformation ell j] A := by
    exact measurableSet_lt measurable_const
      (jointMasterPosterior_inner_measurable (graphRawLaw F) ell j r₀ y hc hr hs hg.continuous)
  obtain ⟨B,hB,hsy,hBA⟩ := observation_event_symmetric_representation ell j hA
  let p := ((physicalObservationLaw (graphRawLaw F) K) A).toReal
  have hpB : physicalObservationProbability F ell B = p := by
    change ((physicalObservationLaw (graphRawLaw F) K) (physicalObservationEvent ell B)).toReal = p
    rw [hBA]
  change p < p₀
  by_contra! hnot
  have hp : 0 < p := h₀.trans_le hnot
  obtain ⟨G,hGn,hlaw,hE⟩ := hTilt B hB hsy (by change p₀ ≤ physicalObservationProbability F ell B; rwa [hpB])
  change graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell B))⁻¹ •
    Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict (physicalObservationEvent ell B)) at hlaw
  rw [hpB,hBA] at hlaw
  change formEnergy Z (graphFormVector G) ≤ sInf (Set.range (energy (Z:ℝ)))+3*Z*lam+
    observationFisherConstant*r₀^(-2.02:ℝ)*(Real.log (Real.exp 1/physicalObservationProbability F ell B))^5+δ at hE
  rw [hpB] at hE
  have hple : p ≤ 1 := hpB ▸ physicalObservationProbability_le_one F hn ell B
  have hlog : 0 ≤ Real.log (Real.exp 1/p) := by
    apply Real.log_nonneg
    exact (one_le_div hp).mpr (hple.trans (by nlinarith [Real.add_one_le_exp (1:ℝ)]))
  have hlo : Real.log (Real.exp 1/p) ≤ Real.log (Real.exp 1/p₀) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_left (Real.exp_pos 1).le h₀ hnot
  have hb : formEnergy Z (graphFormVector G) ≤ allSectorEnergy Z+(Z:ℝ)^(7/3:ℝ) := by
    have hcst : 0 ≤ observationFisherConstant*r₀^(-2.02:ℝ) :=
      mul_nonneg observationFisherConstant_pos.le (Real.rpow_nonneg hr.le _)
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog hlo 5) hcst
    change formEnergy Z (graphFormVector G) ≤ sInf (Set.range (energy (Z:ℝ)))+(Z:ℝ)^(7/3:ℝ)
    linarith only [hE,hm,hbudget]
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  have hupper := normalized_inner_event_global_bound (graphRawLaw F)
    (graphFormVector_admissible G hGn) ell j y hi he hc hc1 hr hs hs1 hg hcg hgn hrad hgs hy hA hp (by simpa only [formRawLaw_graph] using hlaw)
    (show (1:ℝ) ≤ Z by exact_mod_cast hZ) (Real.rpow_nonneg (Nat.cast_nonneg Z) _)
    (show (N:ℝ) ≤ 3*Z by exact_mod_cast hcount) hb
  have hPi : Integrable P (physicalObservationLaw (graphRawLaw F) K) :=
    jointMasterPosterior_inner_integrable (graphRawLaw F) ell j r₀ y hi he hc hr hs hg hcg hgn hrad hgs
  have hlower := threshold_event_mean_ge (physicalObservationLaw (graphRawLaw F) K) hPi
    ((observationInformation_le ell j) A hA) (fun z hz => hz.le) hp
  exact (not_le_of_gt (hupper.trans_lt hsmall)) hlower

end CoulombAtom

end

end OAI
