import OAI.Geometry.IsometricImmersion.Pulses.PulseMomentGeometry
import OAI.Geometry.IsometricImmersion.Pulses.PulseSecondXi

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem actual_leading_weighted_moment_eq (g : MetricField) (z : Coord → ℝ)
    (a delta : ℝ) (N : ℕ) {tau : ℝ} (ht : 0 < tau) :
    pulseWeightedMoment a delta tau
      (fun p => 2*forcingCoefficient g z p*pulsePrincipalLeading a N delta tau p) =
      (tau^2/tau^N)*(∫ q in pulsePairRectangle a delta tau,
        forcingCoefficient g z (pulsePairPoint q)*pulseMomentWeight a delta tau q
          ∂volume.prod volume) := by
  have heq (q : ℝ × ℝ) :
      (2*forcingCoefficient g z (pulsePairPoint q)*
        pulsePrincipalLeading a N delta tau (pulsePairPoint q))*pulseTest a tau q.2 =
      (tau^2/tau^N)*(forcingCoefficient g z (pulsePairPoint q)*pulseMomentWeight a delta tau q) := by
    have h0 : pulsePairPoint q 0 = q.2 := by simp [pulsePairPoint,boxPoint]
    have h1 : pulsePairPoint q 1 = q.1 := by simp [pulsePairPoint,boxPoint]
    unfold pulsePrincipalLeading pulseTest pulseMomentWeight
    rw [h0,h1]
    field_simp [ht.ne']
  unfold pulseWeightedMoment
  simp_rw [heq]
  rw [integral_const_mul]

theorem signed_coefficient_weighted_integral_lower
    {a delta tau sigma d0 : ℝ} {D : Coord → ℝ}
    (hD : ContinuousOn D (pulseStrip a delta tau)) (hsigma : |sigma| = 1)
    (hfloor : ∀ p ∈ pulseStrip a delta tau, d0 ≤ sigma*D p) :
    d0*(∫ q in pulsePairRectangle a delta tau, pulseMomentWeight a delta tau q
      ∂volume.prod volume) ≤
      |∫ q in pulsePairRectangle a delta tau,
        D (pulsePairPoint q)*pulseMomentWeight a delta tau q ∂volume.prod volume| := by
  have hDw : ContinuousOn
      (fun q => D (pulsePairPoint q)*pulseMomentWeight a delta tau q)
      (pulsePairRectangle a delta tau) :=
    (hD.comp pulsePairPoint_continuous.continuousOn (fun _ hq => pulsePairPoint_mem hq)).mul
      (pulseMomentWeight_continuous a delta tau).continuousOn
  have hDi : IntegrableOn
      (fun q => D (pulsePairPoint q)*pulseMomentWeight a delta tau q)
      (pulsePairRectangle a delta tau) (volume.prod volume) :=
    hDw.integrableOn_compact (pulsePairRectangle_isCompact a delta tau)
  have hwi : IntegrableOn (pulseMomentWeight a delta tau)
      (pulsePairRectangle a delta tau) (volume.prod volume) :=
    (pulseMomentWeight_continuous a delta tau).continuousOn.integrableOn_compact
    (pulsePairRectangle_isCompact a delta tau)
  have hmono : d0*(∫ q in pulsePairRectangle a delta tau, pulseMomentWeight a delta tau q
      ∂volume.prod volume) ≤ sigma*(∫ q in pulsePairRectangle a delta tau,
        D (pulsePairPoint q)*pulseMomentWeight a delta tau q ∂volume.prod volume) := by
    have h := integral_mono_ae (hwi.const_mul d0) (hDi.const_mul sigma) (by
      filter_upwards [ae_restrict_mem (pulsePairRectangle_isCompact a delta tau).measurableSet] with q hq
      have hp := mul_le_mul_of_nonneg_right (hfloor _ (pulsePairPoint_mem hq))
        (pulseMomentWeight_nonneg a delta tau q)
      simpa only [mul_assoc] using hp)
    simpa only [integral_const_mul] using h
  apply hmono.trans
  calc
    _ ≤ |sigma*(∫ q in pulsePairRectangle a delta tau,
        D (pulsePairPoint q)*pulseMomentWeight a delta tau q ∂volume.prod volume)| := le_abs_self _
    _ = _ := by rw [abs_mul,hsigma,one_mul]

theorem exists_actual_leading_forcing_moment_lower {a e c : ℝ}
    (ha : 0 < a) (he : 0 < e) (hc : 0 < c) (D C : ℝ) (N : ℕ) :
    ∃ c3 : ℝ, 0 < c3 ∧ ∀ᶠ tau : ℝ in atTop,
      ∀ delta : ℝ, 0 < delta → ∀ (g : MetricField) (z : Coord → ℝ) (U : Set Coord),
        SmoothPositiveOn g U → ContDiffOn ℝ ∞ z U → IsOpen U →
        pulseStrip a delta tau ⊆ U →
        (∀ p ∈ pulseStrip a delta tau, e ≤ heightEnergy g z p) →
        (∀ p ∈ pulseStrip a delta tau, (g p).det ≤ D) →
        (∀ p ∈ pulseStrip a delta tau, c ≤ |covHessian g z p 0 0|) →
        (∀ p ∈ pulseStrip a delta tau, |covHessian g z p 0 0| ≤ C) →
        c3*delta*tau/tau^N ≤
          |pulseWeightedMoment a delta tau
            (fun p => 2*forcingCoefficient g z p*pulsePrincipalLeading a N delta tau p)| := by
  obtain ⟨cs,hcs,hspatial⟩ := spatialCutoff_cos_sq_moment_eventually_lower ha
  let c3 := forcingFloor e D C*(∫ theta : ℝ, temporalCutoff theta)*cs
  have hc3 : 0 < c3 := mul_pos
    (mul_pos (forcingFloor_pos he D C) temporalCutoff_integral_pos) hcs
  refine ⟨c3,hc3,?_⟩
  filter_upwards [hspatial,eventually_gt_atTop (0 : ℝ)] with tau hspatialTau ht
  intro delta hd g z U hg hz hU hSU hE hdet hxx hxxup
  obtain ⟨sigma,hsigma,hsigned⟩ := actual_forcingCoefficient_signed_floor hg hz hU hSU
    (closedRectangle_isPreconnected (-a) a (-(delta/tau)) (delta/tau))
    (pulseStrip_zero_mem ha.le hd.le ht) he hc hE hdet hxx hxxup
  have hxxne : ∀ p ∈ pulseStrip a delta tau, covHessian g z p 0 0 ≠ 0 := by
    intro p hp hz0
    have h := hxx p hp
    rw [hz0,abs_zero] at h
    linarith
  have hcont := (forcingCoefficient_contDiffOn hg hz hU hSU hxxne).continuousOn
  have hmoment := signed_coefficient_weighted_integral_lower hcont hsigma
    (fun p hp => (hsigned p hp).2)
  rw [pulseMomentWeight_integral ha hd ht] at hmoment
  have hscale : 0 ≤ tau^2/tau^N := div_nonneg (sq_nonneg tau) (pow_nonneg ht.le N)
  rw [actual_leading_weighted_moment_eq g z a delta N ht,abs_mul,abs_of_nonneg hscale]
  calc
    c3*delta*tau/tau^N = (tau^2/tau^N)*
      (forcingFloor e D C*((delta/tau)*(∫ theta : ℝ, temporalCutoff theta)*cs)) := by
        dsimp only [c3]
        field_simp [ht.ne']
    _ ≤ (tau^2/tau^N)*(forcingFloor e D C*((delta/tau)*
        (∫ theta : ℝ, temporalCutoff theta)*
          (∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2))) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      apply mul_le_mul_of_nonneg_left _ (forcingFloor_pos he D C).le
      exact mul_le_mul_of_nonneg_left hspatialTau
        (mul_nonneg (div_nonneg hd.le ht.le) temporalCutoff_integral_pos.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left hmoment hscale

end SmoothLocal.Pulse

end

end OAI
