import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.ActualLowInverseBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_FreshRetainedMass_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators NNReal ENNReal

open CoulombAnalysis CoulombNeumann

lemma compact_test_le_mass {R : ℝ} (σ : TFLp (ballMeasure R)) (hσ : NonnegDensity σ)
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) {r q B : ℝ}
    (hs : Function.support k ⊆ closedBall 0 r) (hrq : r < q) (hb : ∀ z, k z ≤ B) :
    (∫ z, k z*σ z ∂ballMeasure R) ≤ B*(∫ z in ball (0 : Space) q, σ z ∂ballMeasure R) := by
  have hi : Integrable σ (ballMeasure R) := (Lp.memLp σ).integrable (Fact.out : (1 : ℝ≥0∞) ≤ 5/3)
  have hki : MemLp k (5/2) (ballMeasure R) := by
    simpa only [zero_add] using centered_test_memLp 0 R hk hs
  calc
    _ ≤ ∫ z, (ball (0 : Space) q).indicator (fun z => B*σ z) z ∂ballMeasure R := by
      apply integral_mono_ae (hki.integrable_mul (Lp.memLp σ))
        ((hi.const_mul B).indicator measurableSet_ball)
      filter_upwards [hσ] with z hz
      by_cases hzin : z ∈ ball (0 : Space) q
      · rw [indicator_of_mem hzin]
        exact mul_le_mul_of_nonneg_right (hb z) hz
      · rw [indicator_of_notMem hzin]
        have hzk : z ∉ Function.support k := by
          intro hzsup
          exact hzin (lt_of_le_of_lt (hs hzsup) hrq)
        change k z*σ z ≤ 0
        rw [Function.notMem_support.mp hzk,zero_mul]
    _ = _ := by rw [integral_indicator measurableSet_ball,integral_const_mul]

lemma masterCenteredKernel_amplitude : ∃ A : ℝ, 0 < A ∧ ∀ {c₁ r₀ s : ℝ},
    0 < c₁ → c₁ < (10*(100000:ℝ))⁻¹ → 0 < r₀ → 0 < s → s ≤ 1 → ∀ y x,
    masterCenteredKernel c₁ r₀ s canonicalRealPacket y x ≤ A*(masterWidth c₁ r₀ s y)⁻¹^3 := by
  obtain ⟨A,hA,hb⟩ := CoulombBarrier.masterKernel_amplitude canonicalRealPacket_smooth.continuous
    canonicalRealPacket_support
  refine ⟨A+1,by linarith,?_⟩
  intro c₁ r₀ s hc hcL hr hs hs1 y x
  exact (hb hc hcL hr hs hs1 (y+x) y).trans (mul_le_mul_of_nonneg_right (by linarith)
    (pow_nonneg (inv_nonneg.mpr (masterWidth_pos hc hr hs y).le) 3))

def canonicalMasterAmplitude : ℝ := Classical.choose masterCenteredKernel_amplitude

lemma canonicalMasterAmplitude_pos : 0 < canonicalMasterAmplitude :=
  (Classical.choose_spec masterCenteredKernel_amplitude).1

lemma canonicalMasterAmplitude_bound {c₁ r₀ s : ℝ} (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y x : Space) :
    masterCenteredKernel c₁ r₀ s canonicalRealPacket y x ≤
      canonicalMasterAmplitude*(masterWidth c₁ r₀ s y)⁻¹^3 :=
  (Classical.choose_spec masterCenteredKernel_amplitude).2 hc hcL hr hs hs1 y x

end Work_FreshRetainedMass_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff NNReal

open CoulombAnalysis CoulombObservation CoulombNeumann
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

 def freshHighThreshold (y : Space) (R H eta : ℝ) (c₁ r₀ s : ℝ) : ℝ :=
  (max (H+(tfPatchOscillationConstant/R*(3*masterWidth c₁ r₀ s y))*R⁻¹^4) 0/
    ((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
    (∫ x, masterCenteredKernel c₁ r₀ s canonicalRealPacket y x ∂ballMeasure R)+
  Real.sqrt ((16*(3*masterWidth c₁ r₀ s y)^3*
    ((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
      (masterWidth c₁ r₀ s y)⁻¹^4)^2)*eta)

lemma threshold_event_mean_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hi : Integrable f μ) {A : Set Ω} (hA : MeasurableSet A)
    {θ : ℝ} (hθ : ∀ z ∈ A, f z ≤ θ) (hp : 0 < (μ A).toReal) :
    (μ A).toReal⁻¹*(∫ z in A, f z ∂μ) ≤ θ := by
  have hh := threshold_event_mean_ge μ hi.neg hA (t := -θ) (fun z hz => by dsimp; linarith [hθ z hz]) hp
  change -θ ≤ (μ A).toReal⁻¹*(∫ z in A, -(f z) ∂μ) at hh
  rw [integral_neg] at hh
  linarith

 theorem TailTiltState.high_inverse_event {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) (k : Fin K) (hk : j.val ≤ k.val)
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) (hry : r₀ ≤ ‖y‖)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hq : 0 < q) (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3))
    (hqk : 3*masterWidth c₁ r₀ s y ≤ (5*localCellRadius y-4*b)/12)
    {H eta m T Q θ : ℝ} (hH : 0 ≤ H) (heta : 0 < eta) (hm : 0 < m)
    (hosc : ∀ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y),
      tfPatchOscillationConstant/(t-4*b)*(3*masterWidth c₁ r₀ s y) ≤ 1/2)
    (hdensity : ∀ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y),
      max (freshHighThreshold y (t-4*b) H eta c₁ r₀ s)
        (canonicalMasterAmplitude*(masterWidth c₁ r₀ s y)⁻¹^3*m)+
      Q*((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
        (masterWidth c₁ r₀ s y)⁻¹^4*Real.sqrt 3*(b+2*dyadicObservationWidth r k)) < T)
    (hsmall : ∀ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y),
      θ+(sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) q+
        sharpLocalPotentialBudget (localCellRadius y)
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (2*masterWidth c₁ r₀ s y)) <
      H-(H/eta+2/m)*(dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ+
          sharpPatchRemainder (localCellRadius y) b
            (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y))-
        2*(tfPatchOscillationConstant/(t-4*b)*(3*masterWidth c₁ r₀ s y))*(t-4*b)⁻¹^4) :
    ((physicalObservationLaw (graphRawLaw F) K)
      {z | Z/‖y‖-lam-tfPotential (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
          (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z)) y ≤ θ ∧
        T ≤ jointMasterPosterior (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
          j c₁ r₀ s canonicalRealPacket (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z) y ∧
        observedLocalCount (fun k : Fin K => dyadicObservationWidth r k) k y
          (2*masterWidth c₁ r₀ s y+Real.sqrt 3*(b+dyadicObservationWidth r k)) z ≤ Q}).toReal < p₀ j := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let pot := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
      (originalDatum ell j z)) y
  let dens := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket (originalDatum ell j z) y
  let A := {z | Z/‖y‖-lam-pot z ≤ θ ∧ T ≤ dens z ∧
    observedLocalCount ell k y (2*masterWidth c₁ r₀ s y+Real.sqrt 3*(b+ell k)) z ≤ Q}
  have hA : MeasurableSet[observationInformation ell j] A :=
    (measurableSet_le (measurable_const.sub
      (jointMasterPosterior_potential_measurable (graphRawLaw F) ell j y hc hr₀ hs canonicalRealPacket_smooth.continuous)) measurable_const).inter
      ((measurableSet_le measurable_const (jointMasterPosterior_value_measurable (graphRawLaw F) ell j y hc hr₀ hs)).inter
        (measurableSet_le (observedLocalCount_information_measurable ell k hk y _) measurable_const))
  change ((physicalObservationLaw (graphRawLaw F) K) A).toReal < p₀ j
  by_contra! hn
  have hp := (h₀ j).trans_le hn
  obtain ⟨G,t,ht,ht0,hGn,hlaw,hgap,hpot⟩ := hstate.event_radial_comparison hZ hlam h₀
    hc hcL hr₀ hs hs1 j hy ha1 hry hb hba hq hqr hqR hcollar hA hn
  have hψ := graphFormVector_admissible G hGn
  have hmass : formMass (graphFormVector G) = 1 := hψ.2.2.2.2.1
  have ha := localCellRadius_pos hy
  have hw := masterWidth_pos hc hr₀ hs y
  have hnuc : t ≤ ‖y‖ := by
    have hh := ht.2
    unfold localCellRadius at hh
    nlinarith [norm_nonneg y]
  have htb : 7*b < t := by linarith [ht.1]
  have hkr : 2*masterWidth c₁ r₀ s y < t-7*b := by linarith [ht.1]
  have hhigh := event_fresh_high_test_support F G ell (fun k => (dyadicObservationWidth_pos hr k).le)
    k hk y ht0 hb hkr
    (masterKernel_test_lipschitz canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    (masterKernel_test_support canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    ((observationInformation_le ell j) A hA) hlaw
    (max (freshHighThreshold y (t-4*b) H eta c₁ r₀ s)
      (canonicalMasterAmplitude*(masterWidth c₁ r₀ s y)⁻¹^3*m)) Q
    (by
      filter_upwards [jointMasterPosterior_eq_scalar (graphRawLaw F) ell j hc hcL hr₀ hs hs1
        canonicalRealPacket_smooth canonicalRealPacket_support y] with z hz
      intro hzA
      refine ⟨?_,hzA.2.2⟩
      have hden := hzA.2.1
      dsimp only [dens] at hden
      rw [←hz] at hden
      exact (hdensity t ht).trans_le hden)
  have hcount : ∀ c : Fin N → Fin 2, ∀ spin : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht0 hb)
        (coreFirstRadialCut_partition y ht0 hb) (graphFormVector G) c) spin u) ≠ 0 →
      m ≤ ∫ z in ball (0 : Space) (3*masterWidth c₁ r₀ s y),
        retainedPatchLp hb (radialPatchRetention N y t b c spin u) u y (t-4*b) z ∂ballMeasure (t-4*b) := by
    intro c spin
    filter_upwards [hhigh c spin] with u hu
    intro hmu
    have htest := compact_test_le_mass
      (retainedPatchLp hb (radialPatchRetention N y t b c spin u) u y (t-4*b))
      (retainedPatchLp_nonneg hb _ _ _ _)
      (masterCenteredKernel_lipschitz canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
      (masterCenteredKernel_support canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
      (by linarith : 2*masterWidth c₁ r₀ s y < 3*masterWidth c₁ r₀ s y)
      (canonicalMasterAmplitude_bound hc hcL hr₀ hs hs1 y)
    have hh := ((le_max_right _ _).trans_lt (hu hmu)).le.trans htest
    exact (mul_le_mul_iff_of_pos_left (mul_pos canonicalMasterAmplitude_pos (pow_pos (inv_pos.mpr hw) 3))).mp hh
  have hcmean := radial_high_mean_expected_center hψ.sobolevFermion y ht0 hb htb hnuc hZ hlam
    (masterCenteredKernel_lipschitz canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    (fun x => masterKernel_nonneg c₁ r₀ s canonicalRealPacket (y+x) y)
    (by linarith : 0 < 3*masterWidth c₁ r₀ s y)
    ((masterCenteredKernel_support canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y).trans
      (closedBall_subset_closedBall (by linarith)))
    (by linarith [ht.1] : 3*masterWidth c₁ r₀ s y ≤ (t-4*b)/12) (hosc t ht) hH heta hm hcount
    (by
      intro c spin
      filter_upwards [hhigh c spin] with u hu
      intro hmu
      exact (le_max_left _ _).trans_lt (hu hmu))
  rw [hmass,mul_one,mul_one] at hcmean
  have hcoef : 0 ≤ H/eta+2/m := by positivity
  have hcenter := (sub_le_sub_right (sub_le_sub_left (mul_le_mul_of_nonneg_left hgap hcoef) H)
    (2*(tfPatchOscillationConstant/(t-4*b)*(3*masterWidth c₁ r₀ s y))*(t-4*b)⁻¹^4)).trans hcmean
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  have hPi := jointMasterPosterior_potential_integrable (graphRawLaw F) ell j y hi he hc hr₀ hs
    canonicalRealPacket_smooth canonicalRealPacket_compact canonicalRealPacket_normalized
    canonicalRealPacket_radial canonicalRealPacket_support
  have hupper := threshold_event_mean_le (physicalObservationLaw (graphRawLaw F) K)
    ((integrable_const (Z/‖y‖-lam)).sub hPi) ((observationInformation_le ell j) A hA)
    (fun z hz => hz.1) hp
  simp only [Pi.sub_apply] at hupper
  rw [normalized_setIntegral_const_sub _ A hPi hp] at hupper
  have hplower := (abs_le.mp hpot).1
  have hstrict := hsmall t ht
  linarith

end CoulombAtom

end

end OAI
