import OAI.Dynamics.StandardMap.MiddleObservationBridge

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def fastBridgeConstant : ℝ≥0∞ := 5*middleBridgeConstant
lemma fastBridgeConstant_ne_top : fastBridgeConstant≠∞ := by
  exact ENNReal.mul_ne_top (by norm_num) middleBridgeConstant_ne_top
lemma actual_fast_bridge_product (k : ℝ) (hc : BridgeScalarControl k)
    (N r : ℕ) (hN : 100 ≤ N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
    {Rw Rh : ℕ} (aw : Fin Rw → ℤ) (nw : Fin Rw → ℕ) (Fw : (Fin Rw → ℝ) → ℝ)
    (ah : Fin Rh → ℤ) (nh : Fin Rh → ℕ) (Fh : (Fin Rh → ℝ) → ℝ)
    (hnw : ∀ j, 0 < nw j) (hnh : ∀ j, 0 < nh j) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hlenw : ∀ j, nw j ≤ 2*r) (hlenh : ∀ j, nh j ≤ 2*r)
    (hwinw : ∀ j l, 1 ≤ l → l ≤ nw j → (aw j+(l:ℤ)-1).natAbs ≤ r)
    (hwinh : ∀ j l, 1 ≤ l → l ≤ nh j → (ah j+(l:ℤ)-1-(N:ℤ)).natAbs ≤ r)
    (hW0 : ∀ z, 0 ≤ shortfallObservation k aw nw Fw z)
    (hlog : 1 ≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L ≤ growthBase k)
    (h : ℝ) (hδ : growthBase k^(-(1/10:ℝ)*(N:ℝ)) < h/2) :
    (∫⁻ z in {z | torusFastBridge k z N} ∩ {z | h < shortfallObservation k ah nh Fh z},
      ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area) ≤
      fastBridgeConstant*((∫⁻ z, ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area)+
        ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*
          area {z | h/2 < shortfallObservation k ah nh Fh z} := by
  classical
  let W := shortfallObservation k aw nw Fw
  let H := shortfallObservation k ah nh Fh
  have hW : Continuous W := continuous_shortfall_observation k hc.nonneg _ _ _ hFw.continuous
  have hH : Continuous H := continuous_shortfall_observation k hc.nonneg _ _ _ hFh.continuous
  let E : ℕ → Set Torus := fun i => (torusIter k (i:ℤ) ⁻¹' middlePrefixEvent k (N-i) i) ∩ {z | h < H z}
  let F : Set Torus := {z | torusFastBridge k z N} ∩ {z | h < H z}
  have hE (i : ℕ) : MeasurableSet (E i) :=
    ((measurableSet_middlePrefixEvent k (N-i) i).preimage (continuous_torusIter k _).measurable).inter
      (isOpen_lt continuous_const hH).measurableSet
  have hF : MeasurableSet F := (measurableSet_torusFastBridge k N).inter (isOpen_lt continuous_const hH).measurableSet
  have hEeq : E = (fun i : ℕ => (torusIter k (i:ℤ) ⁻¹' middlePrefixEvent k (N-i) i) ∩ {z | h < H z}) := rfl
  clear_value E
  have hcovers := lintegral_count_cover area (bridgeMiddle N) E (fun i _ => hE i) F hF
    (fun z => ENNReal.ofReal (W z)) hW.measurable.ennreal_ofReal ((N:ℝ)/5) (by
      intro z hz
      have hcount := torus_good_middles_count k hc.nonneg N hN z hz.1
      apply hcount.trans
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro i hi
      simp only [torusGoodMiddles,Finset.mem_filter] at hi
      rw [Finset.mem_filter]
      refine ⟨hi.1,?_⟩
      rw [hEeq]
      exact ⟨hi.2,hz.2⟩)
  let K := middleBridgeConstant*((∫⁻ z, ENNReal.ofReal (W z) ∂area)+
      ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*area {z | h/2 < H z}
  have hsum : (∑ i∈bridgeMiddle N, ∫⁻ z in E i, ENNReal.ofReal (W z) ∂area) ≤ (N:ℝ≥0∞)*K := by
    calc
      _ ≤ ∑ _i∈bridgeMiddle N, K := Finset.sum_le_sum fun i hi => by
        rw [hEeq]
        exact middle_observation_product k hc N r i hN hi hr aw nw Fw ah nh Fh hnw hnh L hFw hFh
          hlenw hlenh hwinw hwinh hW0 hlog hLM h hδ
      _ = ((bridgeMiddle N).card:ℝ≥0∞)*K := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ bot_le
        apply Nat.cast_le.mpr
        calc
          (bridgeMiddle N).card ≤ (Finset.range N).card := Finset.card_le_card (by
            intro i hi
            have hb := bridgeMiddle_bounds N i hN hi
            exact Finset.mem_range.mpr (by omega))
          _ = N := Finset.card_range N
  have hpos : 0 < (N:ℝ)/5 := by
    have : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  have hetop : ENNReal.ofReal ((N:ℝ)/5)≠∞ := ENNReal.ofReal_ne_top
  have hemul : (N:ℝ≥0∞)*K=ENNReal.ofReal ((N:ℝ)/5)*(5*K) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<5),ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
    calc
      _ = ((N:ℝ≥0∞)/5*5)*K := by rw [ENNReal.div_mul_cancel (by norm_num : (5:ℝ≥0∞)≠0) (by norm_num : (5:ℝ≥0∞)≠∞)]
      _ = _ := by ac_rfl
  have htot := hcovers.trans hsum
  rw [hemul] at htot
  have hfinal := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hpos).ne' hetop).mp htot
  simpa only [F,W,H,K,fastBridgeConstant,mul_assoc] using hfinal
end StandardMapEntropy

end OAI
