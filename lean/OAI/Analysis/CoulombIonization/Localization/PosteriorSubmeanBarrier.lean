import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BoundedL1PotentialBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierObservationTowerBarrier
import OAI.Analysis.CoulombIonization.Localization.ActualPointInverseBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric

open CoulombAnalysis CoulombObservation CoulombBarrier

lemma bounded_L1_pair_integrable {ρ η : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    (hmη : Measurable η) (hiη : Integrable η) :
    Integrable (fun p : Space × Space => η p.1*ρ p.2/‖p.1-p.2‖) := by
  rw [Measure.volume_eq_prod]
  have hj : Measurable (fun p : Space × Space => η p.1*ρ p.2/‖p.1-p.2‖) :=
    ((hmη.comp measurable_fst).mul (hm.comp measurable_snd)).div
      (measurable_fst.sub measurable_snd).norm
  apply (integrable_prod_iff hj.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun x => by
      simpa only [mul_div_assoc] using
        (bounded_L1_potential_integrable hm hi hM hn hb x).const_mul (η x)
  · have hpot := (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous
    have hprod : Integrable (fun x => ‖η x‖*tfPotential ρ x) := by
      apply (hiη.norm.mul_const (2*Real.pi*M+∫ z, ρ z)).mono'
        (hmη.norm.mul hpot.measurable).aestronglyMeasurable
      exact ae_of_all _ fun x => by
        change ‖‖η x‖*tfPotential ρ x‖ ≤ _
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (tfPotential_nonneg (ae_of_all _ hn) x))]
        exact mul_le_mul_of_nonneg_left (bounded_L1_potential_le hm hi hM hn hb x) (norm_nonneg _)
    have he : (fun x => ∫ z, ‖η x*ρ z/‖x-z‖‖) =
        (fun x => ‖η x‖*tfPotential ρ x) := by
      funext x
      simp only [mul_div_assoc,norm_mul,
        Real.norm_of_nonneg (div_nonneg (hn _) (norm_nonneg _)),
        integral_const_mul,tfPotential]
    change Integrable (fun x => ∫ z, ‖η x*ρ z/‖x-z‖‖)
    rw [he]
    exact hprod

lemma bounded_L1_potential_radial_average_le {ρ η : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    (hmη : Measurable η) {R B : ℝ} (hR : 0 ≤ R)
    (hnη : ∀ z, 0 ≤ η z) (hsη : ∀ z, η z ≠ 0 → ‖z‖ ≤ R)
    (hbη : ∀ z, |η z| ≤ B) (hrη : IsRadial η) (h1η : ∫ z, η z = 1) (y : Space) :
    (∫ z, tfPotential ρ z*η (z-y)) ≤ tfPotential ρ y := by
  have hsupport : Function.support η ⊆ closedBall 0 R :=
    fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hsη x hx
  have hiη := bounded_compact_integrable hmη (isCompact_closedBall _ _) hsupport hbη
  have hpη := bounded_compact_memLp hmη (isCompact_closedBall _ _) hsupport hbη (5/3)
  have htη := bounded_compact_integrable (translatedDensity_measurable hmη y)
    (isCompact_closedBall y R) (translatedDensity_support hsη y) (fun _ => hbη _)
  have hpair := bounded_L1_pair_integrable hm hi hM hn hb
    (translatedDensity_measurable hmη y) htη
  calc
    _ = ∫ z, translatedDensity η y z*tfPotential ρ z := by
      apply integral_congr_ae; exact ae_of_all _ fun _ => mul_comm _ _
    _ = ∫ z, ρ z*tfPotential (translatedDensity η y) z := coulomb_potential_pair_comm hpair
    _ ≤ tfPotential ρ y := by
      have hswap : Integrable (fun p : Space × Space => ρ p.1*translatedDensity η y p.2/‖p.1-p.2‖) := by
        have hh := hpair
        rw [Measure.volume_eq_prod] at hh ⊢
        apply hh.swap.congr
        exact ae_of_all _ fun p => by dsimp; rw [norm_sub_rev]; ring
      apply integral_mono_ae (coulomb_potential_pair_integrable hswap)
        (bounded_L1_potential_integrable hm hi hM hn hb y)
      filter_upwards [volume.ae_ne y] with z hz
      rw [potential_translatedDensity]
      have hd := radial_potential_le_point hiη hpη hnη hrη hR hsη (sub_ne_zero.mpr hz)
      rw [h1η] at hd
      have hh := mul_le_mul_of_nonneg_left hd (hn z)
      simpa only [norm_sub_rev y z,div_eq_mul_inv,one_div,one_mul] using hh

theorem bounded_L1_field_radial_submean {ρ η : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    (hmη : Measurable η) {R B : ℝ} (hR : 0 < R)
    (hnη : ∀ z, 0 ≤ η z) (hsη : ∀ z, η z ≠ 0 → ‖z‖ ≤ R)
    (hbη : ∀ z, |η z| ≤ B) (hrη : IsRadial η) (h1η : ∫ z, η z = 1)
    (y : Space) (hnuc : R ≤ ‖y‖) (Z lam : ℝ) :
    Z/‖y‖-lam-tfPotential ρ y ≤
      ∫ z, (Z/‖z‖-lam-tfPotential ρ z)*η (z-y) := by
  let k := translatedDensity η y
  have hkm : Measurable k := translatedDensity_measurable hmη y
  have hks := translatedDensity_support hsη y
  have hki : Integrable k := bounded_compact_integrable hkm (isCompact_closedBall y R) hks (fun _ => hbη _)
  have hkp : MemLp k (5/3) := bounded_compact_memLp hkm (isCompact_closedBall y R) hks (fun _ => hbη _) _
  have hk1 : (∫ z, k z) = 1 := by rw [translatedDensity_mass,h1η]
  have hknuc : Integrable (fun z => Z/‖z‖*k z) := by
    have hh := (tfPotential_integrable hki hkp (0:Space)).const_mul Z
    apply hh.congr
    exact ae_of_all _ fun z => by
      dsimp only
      rw [zero_sub,norm_neg]
      ring
  have hkpot : Integrable (fun z => tfPotential ρ z*k z) := by
    simpa only [mul_comm] using coulomb_potential_pair_integrable (bounded_L1_pair_integrable hm hi hM hn hb hkm hki)
  have hnucint : (∫ z, Z/‖z‖*k z) = Z/‖y‖ := by
    calc
      _ = Z*tfPotential k 0 := by
        rw [tfPotential,←integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun z => by dsimp; rw [zero_sub,norm_neg]; ring
      _ = _ := by
        rw [radial_translatedDensity_potential hmη hR hsη hbη hrη h1η y 0
          (by simpa only [zero_sub,norm_neg] using hnuc),zero_sub,norm_neg]
        ring
  have hp := bounded_L1_potential_radial_average_le hm hi hM hn hb hmη hR.le hnη hsη hbη hrη h1η y
  change _ ≤ ∫ z, (Z/‖z‖-lam-tfPotential ρ z)*k z
  simp_rw [sub_mul]
  have hsub : Integrable (fun z => Z/‖z‖*k z-lam*k z) := hknuc.sub (hki.const_mul lam)
  rw [integral_sub hsub hkpot,
    integral_sub hknuc (hki.const_mul lam),integral_const_mul,hk1,mul_one,hnucint]
  exact sub_le_sub_left hp _

open MeasureTheory Set Metric

open CoulombAnalysis CoulombObservation CoulombBarrier

lemma ballAverageKernel_average (f : Space → ℝ) (y : Space) (R : ℝ) :
    (∫ z, f z*ballAverageKernel R (z-y)) =
      (1/(R^3*(Real.pi*4/3)))*(∫ z in closedBall y R, f z) := by
  rw [←integral_const_mul,←integral_indicator isClosed_closedBall.measurableSet]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    have hz : z-y ∈ closedBall (0:Space) R ↔ z ∈ closedBall y R := by
      simp only [mem_closedBall,dist_eq_norm,sub_zero]
    by_cases h : z ∈ closedBall y R
    · simp only [ballAverageKernel,indicator_of_mem h,indicator_of_mem (hz.mpr h)]
      ring
    · simp only [ballAverageKernel,indicator_of_notMem h,indicator_of_notMem (mt hz.mp h),mul_zero]

lemma bounded_L1_field_ball_submean {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) {R : ℝ} (hR : 0 < R)
    (y : Space) (hnuc : R ≤ ‖y‖) (Z lam : ℝ) :
    Z/‖y‖-lam-tfPotential ρ y ≤
      (1/(R^3*(Real.pi*4/3)))*(∫ z in closedBall y R, Z/‖z‖-lam-tfPotential ρ z) := by
  simpa only [ballAverageKernel_average] using
    bounded_L1_field_radial_submean hm hi hM hn hb
      (ballAverageKernel_measurable R) hR (ballAverageKernel_nonneg hR)
      (ballAverageKernel_support R) (ballAverageKernel_bound hR)
      (ballAverageKernel_radial R) (ballAverageKernel_mass hR) y hnuc Z lam

lemma originalQueryDensity_bounded_L1 {N K : ℕ} (F : fermionGraph N)
    (r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ),
      Measurable (originalQueryDensity F r j c₁ r₀ s z) ∧
      Integrable (originalQueryDensity F r j c₁ r₀ s z) ∧
      (∀ y, 0 ≤ originalQueryDensity F r j c₁ r₀ s z y) ∧
      (∀ y, originalQueryDensity F r j c₁ r₀ s z y ≤ M) := by
  let ell := fun k : Fin K => dyadicObservationWidth r k
  have hm := originalMasterField_measurable (graphRawLaw F) ell j hc hr₀ hs
    canonicalRealPacket_smooth.continuous
  obtain ⟨M,hM,hb⟩ := jointMasterPosterior_global_bound (graphRawLaw F) ell j hc hr₀ hs hrs
    canonicalRealPacket_smooth.continuous canonicalRealPacket_compact
  refine ⟨M,hM,fun z => ⟨?_,?_,?_,?_⟩⟩
  · exact hm.comp ((measurable_const (a := z)).prodMk measurable_id)
  · exact jointMasterPosterior_integrable (graphRawLaw F) ell j hc hr₀ hs
      canonicalRealPacket_smooth.continuous canonicalRealPacket_normalized (originalDatum ell j z)
  · exact jointMasterPosterior_nonneg (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
      (originalDatum ell j z)
  · intro y
    apply (le_abs_self _).trans
    change |jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket (originalDatum ell j z) y| ≤ M
    simpa only [Real.norm_eq_abs] using hb (originalDatum ell j z) y

theorem originalQueryField_ball_submean {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    {R : ℝ} (hR : 0 < R) (y : Space) (hnuc : R ≤ ‖y‖) :
    originalQueryField F Z lam r j c₁ r₀ s z y ≤
      (1/(R^3*(Real.pi*4/3)))*(∫ x in closedBall y R,
        originalQueryField F Z lam r j c₁ r₀ s z x) := by
  obtain ⟨M,hM,hρ⟩ := originalQueryDensity_bounded_L1 F r j hc hr₀ hs hrs
  exact bounded_L1_field_ball_submean (hρ z).1 (hρ z).2.1 hM (hρ z).2.2.1
    (hρ z).2.2.2 hR y hnuc Z lam

end CoulombAtom

end

end OAI
