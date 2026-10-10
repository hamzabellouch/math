import OAI.Geometry.IsometricImmersion.Pulses.PulseTemporalMoment
import OAI.Geometry.IsometricImmersion.Comparison.ActualComparisonEquation
import OAI.Geometry.IsometricImmersion.Caps.EllipticAbsorption

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor
open SmoothLocal.HighEquation

def testedOperatorSource (R S b c v : Coord → ℝ) (p : Coord) : ℝ :=
  hyperbolicOperator R S v p-b p*coordPartial 1 v p-c p*coordPartial 0 v p

theorem testedOperatorSource_contDiffOn {R S b c v : Coord → ℝ} {U : Set Coord}
    (hR : ContDiffOn ℝ ∞ R U) (hS : ContDiffOn ℝ ∞ S U)
    (hb : ContDiffOn ℝ ∞ b U) (hc : ContDiffOn ℝ ∞ c U)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (testedOperatorSource R S b c v) U :=
  ((((partial_contDiffOn (partial_contDiffOn hv hU 1) hU 1).sub
    (hR.mul (partial_contDiffOn (partial_contDiffOn hv hU 1) hU 0))).sub
    (hS.mul (partial_contDiffOn (partial_contDiffOn hv hU 0) hU 0))).sub
    (hb.mul (partial_contDiffOn hv hU 1))).sub (hc.mul (partial_contDiffOn hv hU 0))

theorem pulseWeightedMoment_eq_tested_rectangle {a delta tau : ℝ} {f : Coord → ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hf : ContinuousOn f (pulseStrip a delta tau)) :
    pulseWeightedMoment a delta tau f =
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau) (fun p => pulseSpatialTest a tau p*f p) := by
  have hh := pulsePair_integral_eq_rectangleIntegral ha.le hd ht
    ((pulseSpatialTest_contDiff a tau).continuous.continuousOn.mul hf)
  simp only [Pi.mul_def] at hh
  have he : (fun q : ℝ × ℝ => pulseSpatialTest a tau (pulsePairPoint q)*f (pulsePairPoint q)) =
      (fun q => f (pulsePairPoint q)*pulseTest a tau q.2) := by
    funext q
    simp only [pulseSpatialTest,pulsePairPoint,pulse_boxPoint_zero,mul_comm]
  rw [he] at hh
  exact hh

theorem testedOperatorSource_moment_identity {a delta tau : ℝ}
    {R S b c v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hR : ContDiffOn ℝ ∞ R U) (hS : ContDiffOn ℝ ∞ S U)
    (hb : ContDiffOn ℝ ∞ b U) (hc : ContDiffOn ℝ ∞ c U)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U) :
    pulseWeightedMoment a delta tau (testedOperatorSource R S b c v) =
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p)-
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*R p*coordPartial 0 (coordPartial 1 v) p)-
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial 0 v) p)-
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*b p*coordPartial 1 v p)-
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*c p*coordPartial 0 v p) := by
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hψ : ContinuousOn (pulseSpatialTest a tau) (pulseStrip a delta tau) :=
    (pulseSpatialTest_contDiff a tau).continuous.continuousOn
  have hvi (i : Fin 2) := (partial_contDiffOn hv hU i).continuousOn.mono hSU
  have hvij (i j : Fin 2) := (partial_contDiffOn (partial_contDiffOn hv hU j) hU i).continuousOn.mono hSU
  have h0 := hψ.mul (hvij 1 1)
  have h1 := (hψ.mul (hR.continuousOn.mono hSU)).mul (hvij 0 1)
  have h2 := (hψ.mul (hS.continuousOn.mono hSU)).mul (hvij 0 0)
  have h3 := (hψ.mul (hb.continuousOn.mono hSU)).mul (hvi 1)
  have h4 := (hψ.mul (hc.continuousOn.mono hSU)).mul (hvi 0)
  rw [pulseWeightedMoment_eq_tested_rectangle ha hd ht
    ((testedOperatorSource_contDiffOn hR hS hb hc hv hU).continuousOn.mono hSU)]
  have heq : (fun p => pulseSpatialTest a tau p*testedOperatorSource R S b c v p) =
      fun p => (((pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p-
        pulseSpatialTest a tau p*R p*coordPartial 0 (coordPartial 1 v) p)-
        pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial 0 v) p)-
        pulseSpatialTest a tau p*b p*coordPartial 1 v p)-
        pulseSpatialTest a tau p*c p*coordPartial 0 v p := by
    funext p
    unfold testedOperatorSource hyperbolicOperator
    ring
  have hs4 := rectangleIntegral_sub hlr hbt (((h0.sub h1).sub h2).sub h3) h4
  have hs3 := rectangleIntegral_sub hlr hbt ((h0.sub h1).sub h2) h3
  have hs2 := rectangleIntegral_sub hlr hbt (h0.sub h1) h2
  have hs1 := rectangleIntegral_sub hlr hbt h0 h1
  simp only [Pi.mul_def,Pi.sub_def] at hs4 hs3 hs2 hs1
  rw [heq,hs4,hs3,hs2,hs1]

theorem testedOperatorSource_moment_cost {a delta tau K K1 M B : ℝ} {N : ℕ}
    {R S b c v : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hK : 0 ≤ K) (hK1 : 0 ≤ K1) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hR : ContDiffOn ℝ ∞ R U) (hS : ContDiffOn ℝ ∞ S U)
    (hb : ContDiffOn ℝ ∞ b U) (hc : ContDiffOn ℝ ∞ c U)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hcoeff : ∀ p ∈ pulseStrip a delta tau, |R p| ≤ K ∧ |S p| ≤ K ∧ |b p| ≤ K ∧ |c p| ≤ K)
    (hderiv : ∀ p ∈ pulseStrip a delta tau, |coordPartial 0 R p| ≤ K1 ∧ |coordPartial 0 S p| ≤ K1)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau), ∀ i : Fin 2,
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ M*delta*tau/tau^N)
    (hI : IsOpen I) (hsub : Icc (-a) a ⊆ I)
    (hupper : ∀ x ∈ I, (![x,delta/tau] : Coord) ∈ U)
    (hinitial : ∀ x ∈ Icc (-a) a, coordPartial 1 v (boxPoint x (-(delta/tau))) = 0)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a,
      ‖iteratedFDeriv ℝ k (heightCauchyVelocity v (delta/tau)) x‖ ≤ B) :
    |pulseWeightedMoment a delta tau (testedOperatorSource R S b c v)| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N+
      (4*pulseTestDerivativeBound a ha*K*Real.sqrt (2*a)*M)*delta^2*tau/tau^N+
      (4*axisBumpDerivativeBound a ha 0*(K1+K)*Real.sqrt (2*a)*M)*delta^2/tau^N := by
  have htpos := zero_lt_one.trans_le ht
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd htpos.le]
  have htime := pulse_temporal_moment_finite_bound ha hB hd htpos hv hU hSU hI hsub hupper hinitial N hjet
  have hRcost := pulse_spatial_second_cost 1 ha hd ht hK hK1 hM hR hv hU hSU
    (fun p hp => (hcoeff p hp).1) (fun p hp => (hderiv p hp).1) (fun theta ht => hL2 theta ht 1)
  have hScost := pulse_spatial_second_cost 0 ha hd ht hK hK1 hM hS hv hU hSU
    (fun p hp => (hcoeff p hp).2.1) (fun p hp => (hderiv p hp).2) (fun theta ht => hL2 theta ht 0)
  have hbcost := pulse_test_pairing_extra_inv_tau 1 ha hd ht hK hM hU hSU hb hv
    (fun p hp => (hcoeff p hp).2.2.1) (fun theta ht => hL2 theta ht 1)
  have hccost := pulse_test_pairing_extra_inv_tau 0 ha hd ht hK hM hU hSU hc hv
    (fun p hp => (hcoeff p hp).2.2.2) (fun theta ht => hL2 theta ht 0)
  have hfirst (F : Coord → ℝ) (i : Fin 2) :
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*F p*coordPartial i v p) =
      ∫ theta in Icc (-(delta/tau)) (delta/tau), ∫ x in Icc (-a) a,
        pulseTest a tau x*F (boxPoint x theta)*coordPartial i v (boxPoint x theta) := by
    rw [rectangleIntegral_eq_Icc_slices _ hlr hbt]
    simp only [pulseSpatialTest,pulse_boxPoint_zero]
  rw [testedOperatorSource_moment_identity ha hd htpos hR hS hb hc hv hU hSU]
  rw [← hfirst b 1] at hbcost
  rw [← hfirst c 0] at hccost
  have htriangle (a0 a1 a2 a3 a4 : ℝ) :
      |(((a0-a1)-a2)-a3)-a4| ≤ (((|a0|+|a1|)+|a2|)+|a3|)+|a4| := by
    have h01 := abs_sub a0 a1
    have h02 := (abs_sub (a0-a1) a2).trans (add_le_add h01 le_rfl)
    have h03 := (abs_sub ((a0-a1)-a2) a3).trans (add_le_add h02 le_rfl)
    exact (abs_sub (((a0-a1)-a2)-a3) a4).trans (add_le_add h03 le_rfl)
  calc
    _ ≤ (((|rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p)|+
      |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*R p*coordPartial 0 (coordPartial 1 v) p)|)+
      |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial 0 v) p)|)+
      |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*b p*coordPartial 1 v p)|)+
      |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*c p*coordPartial 0 v p)| := by
      exact htriangle _ _ _ _ _
    _ ≤ _ := by
      have hsum := add_le_add (add_le_add (add_le_add (add_le_add htime hRcost) hScost) hbcost) hccost
      apply hsum.trans_eq
      ring

end SmoothLocal.Pulse

end

end OAI
