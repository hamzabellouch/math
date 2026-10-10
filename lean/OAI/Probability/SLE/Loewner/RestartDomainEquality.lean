import OAI.Probability.SLE.Geometry.RestartGreenKernel
import OAI.Probability.SLE.Gauge.DenseRadiusGap

namespace OAI

/-! Surjectivity of the actual restarted surviving domain. Inverse-map
composition identifies every original future live point with a live fresh
point, so reaching a deeper radius is equivalent in the two charts. -/

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma IsCapacityTwoWitness.restart_live_preimage
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ (T + t)) :
    G T z - (U T : ℂ) ∈ survivingDomain β t := by
  let v := G (T + t) z - (U T : ℂ)
  have hv : v ∈ upperHalfPlane := by
    simpa only [v, upperHalfPlane, mem_ofPred_eq, Complex.sub_im, Complex.ofReal_im, sub_zero]
      using hw.2.2.2.2.2.1 (T + t) hz
  have hvadd : v + (U T : ℂ) = G (T + t) z := sub_add_cancel _ _
  have hcomp := hw.restart_inverse_composition T hb t v hv
  rw [hvadd, hw.2.2.2.2.2.2.2.1 (T + t) z hz] at hcomp
  have hFv : F' t v + (U T : ℂ) ∈ upperHalfPlane := by
    simpa only [upperHalfPlane, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, add_zero]
      using (hb.2.2.2.2.2.2.1 t hv).1.1
  have he : F' t v + (U T : ℂ) = G T z := by
    rw [← hw.2.2.2.2.2.2.2.2.1 T _ hFv, ← hcomp]
  have he' : F' t v = G T z - (U T : ℂ) := by
    rw [← he, add_sub_cancel_right]
  rw [← he']
  exact hb.2.2.2.2.2.2.1 t hv

lemma IsCapacityTwoWitness.restart_domain_iff
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (t : ℝ≥0) (w : ℂ) (hwH : w ∈ upperHalfPlane) :
    F T (w + (U T : ℂ)) ∈ survivingDomain γ (T + t) ↔ w ∈ survivingDomain β t := by
  constructor
  · intro hz
    have hwadd : w + (U T : ℂ) ∈ upperHalfPlane := by
      simpa only [upperHalfPlane, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, add_zero]
        using hwH
    have h := hw.restart_live_preimage T hb t _ hz
    rwa [hw.2.2.2.2.2.2.2.2.1 T _ hwadd, add_sub_cancel_right] at h
  · exact fun ht => (hw.restart_forward_composition T hb t w ht).1

theorem IsCapacityTwoWitness.restart_radius_finite_iff
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (w : ℂ) (hwH : w ∈ upperHalfPlane) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 < v)
    (hbase : fullRadius G T (F T (w + (U T : ℂ))) =
      (2 * (F T (w + (U T : ℂ))).im) * Real.exp (-u)) :
    radiusLevelTime γ G (F T (w + (U T : ℂ))) (u + v) < ∞ ↔
      radiusLevelTime β G' w v < ∞ := by
  have hUp : Continuous (fun t => U (T + t) - U T) :=
    (hU.comp (continuous_const.add continuous_id)).sub continuous_const
  have hwadd : w + (U T : ℂ) ∈ upperHalfPlane := by
    simpa only [upperHalfPlane, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, add_zero] using hwH
  constructor
  · intro hfinite
    obtain ⟨S, hSlive, hSR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G _ (u + v) hfinite
    have hS := radiusLevelTime_eq_of_live_level hU hw _ (u + v) S hSlive hSR
    have hbefore := hw.before_deeper_radius_level hU _ u v hu hv T
      (hw.2.2.2.2.2.2.1 T hwadd) hbase
    rw [hS] at hbefore
    have hTS : T ≤ S := by exact_mod_cast hbefore.le
    let t := S - T
    have htime : T + t = S := add_tsub_cancel_of_le hTS
    have htlive : w ∈ survivingDomain β t :=
      (hw.restart_domain_iff T hb t w hwH).mp (htime ▸ hSlive)
    have hR := hw.restart_radius_composition hU T hb t w htlive
    rw [htime, hSR] at hR
    have hR0 := hw.restart_initial_radius hU T hb w hwH
    rw [hbase] at hR0
    have hD := hw.restart_inverse_derivative_norm_pos hU T hb w hwH
    have hsourceR : fullRadius G' t w = (2 * w.im) * Real.exp (-v) := by
      apply mul_left_cancel₀ hD.ne'
      calc
        _ = (2 * (F T (w + (U T : ℂ))).im) * Real.exp (-(u + v)) := hR.symm
        _ = ((2 * (F T (w + (U T : ℂ))).im) * Real.exp (-u)) * Real.exp (-v) := by
          rw [neg_add, Real.exp_add]
          ring
        _ = _ := by rw [hR0]; ring
    rw [radiusLevelTime_eq_of_live_level hUp hb w v t htlive hsourceR]
    exact ENNReal.coe_lt_top
  · intro hfinite
    obtain ⟨t, ht, hR⟩ := exists_live_level_of_radiusLevelTime_lt_top β G' w v hfinite
    rw [(hw.restart_level_of_live_source hU T hb w u v hbase t ht hR).2]
    exact ENNReal.coe_lt_top

end SLEExactGauge

end

end OAI
