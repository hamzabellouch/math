import OAI.Dynamics.StandardMap.BridgeSamples

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma sample_bridge_integral (k : ℝ) (hc : BridgeScalarControl k)
    (n N r : ℕ) (hn : 0< n) (hN : 100≤ N) (hr : (r:ℝ)≤ (N:ℝ)/1000)
    (u v : DyadicTime) (b : ℤ) (hu : (n:ℝ)*(u:ℝ)=(b:ℝ)) (hv : (n:ℝ)*(v:ℝ)=(b:ℝ)+(N:ℝ))
    {Rw Rh : ℕ} (sw tw : Fin Rw → DyadicTime) (sh th : Fin Rh → DyadicTime)
    (aw : Fin Rw → ℤ) (nw : Fin Rw → ℕ) (Fw : (Fin Rw → ℝ) → ℝ)
    (ah : Fin Rh → ℤ) (nh : Fin Rh → ℕ) (Fh : (Fin Rh → ℝ) → ℝ)
    (hnw : ∀j,0< nw j) (hnh : ∀j,0< nh j)
    (hsw : ∀j,(n:ℝ)*(sw j:ℝ)=((aw j+b):ℤ))
    (htw : ∀j,(n:ℝ)*(tw j:ℝ)=((aw j+b):ℤ)+(nw j:ℝ))
    (hsh : ∀j,(n:ℝ)*(sh j:ℝ)=((ah j+b):ℤ))
    (hth : ∀j,(n:ℝ)*(th j:ℝ)=((ah j+b):ℤ)+(nh j:ℝ))
    (L : NNReal) (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hlenw : ∀j,nw j≤ 2*r) (hlenh : ∀j,nh j≤ 2*r)
    (hwinw : ∀j l,1≤ l → l≤ nw j → (aw j+(l:ℤ)-1).natAbs≤ r)
    (hwinh : ∀j l,1≤ l → l≤ nh j → (ah j+(l:ℤ)-1-(N:ℤ)).natAbs≤ r)
    (hW0 : ∀z,0≤ shortfallObservation k aw nw Fw z)
    (hH0 : ∀z,0≤ shortfallObservation k ah nh Fh z)
    (hlog : 1≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L≤ growthBase k)
    (η : ℝ) (hη : 0<η) (hδ : growthBase k^(-(1/10:ℝ)*(N:ℝ))<η/2)
    (F : DistanceArray → ℝ) (hF : Continuous F) (D : ℝ) (hD : 0≤ D)
    (hFW : ∀d,F d≤ D*arrayObservation sw tw Fw d)
    (hzero : ∀d,¬((999/1000:ℝ)*((v:ℝ)-(u:ℝ))< d.val u v ∧ η< arrayObservation sh th Fh d) → F d=0) :
    (∫ d,F d ∂sampleLaw k hc.nonneg n hn)≤ D*bridgeRealConstant*
      ((∫ d,arrayObservation sw tw Fw d ∂sampleLaw k hc.nonneg n hn)+growthBase k^(-(1/10:ℝ)*(N:ℝ)))*
      ((∫ d,arrayObservation sh th Fh d ∂sampleLaw k hc.nonneg n hn)/(η/2)) := by
  let W := shortfallObservation k aw nw Fw
  let H := shortfallObservation k ah nh Fh
  let E := {z | torusFastBridge k z N} ∩ {z | η< H z}
  have hW : Continuous W := continuous_shortfall_observation k hc.nonneg _ _ _ hFw.continuous
  have hH : Continuous H := continuous_shortfall_observation k hc.nonneg _ _ _ hFh.continuous
  have hiW := hW.integrable_of_hasCompactSupport (μ := area) (HasCompactSupport.of_compactSpace _)
  have hE : MeasurableSet E := (measurableSet_torusFastBridge k N).inter (isOpen_lt continuous_const hH).measurableSet
  have heW (z : Torus) : arrayObservation sw tw Fw (sampleArray k hc.nonneg z n hn)=W (torusIter k b z) := by
    rw [arrayObservation_sample k hc.nonneg n hn sw tw (fun j => aw j+b) nw hnw hsw htw Fw]
    exact (shortfallObservation_shift k aw nw Fw b z).symm
  have heH (z : Torus) : arrayObservation sh th Fh (sampleArray k hc.nonneg z n hn)=H (torusIter k b z) := by
    rw [arrayObservation_sample k hc.nonneg n hn sh th (fun j => ah j+b) nh hnh hsh hth Fh]
    exact (shortfallObservation_shift k ah nh Fh b z).symm
  have hiI : Integrable (fun z => E.indicator W (torusIter k b z)) area :=
    (measurePreserving_torusIter k b).integrable_comp_of_integrable (hiW.indicator hE)
  have hbound : (∫ z,F (sampleArray k hc.nonneg z n hn) ∂area)≤ D*(∫ z in E,W z ∂area) := by
    rw [←integral_indicator hE,←integral_torusIter k b (E.indicator W),←integral_const_mul]
    apply integral_mono ((hF.comp (continuous_sampleArray k hc.nonneg n hn)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (hiI.const_mul D)
    intro z
    dsimp only [Function.comp_apply]
    by_cases hz : torusIter k b z∈E
    · rw [indicator_of_mem hz]
      simpa only [heW] using hFW (sampleArray k hc.nonneg z n hn)
    · rw [indicator_of_notMem hz,mul_zero]
      have hfz : F (sampleArray k hc.nonneg z n hn)=0 := hzero _ (by
        intro h
        apply hz
        exact ⟨array_fast_sample k hc.nonneg z n hn u v b N hu hv h.1,by simpa only [Set.mem_ofPred_eq,←heH z] using h.2⟩)
      exact hfz.le
  have hwint : (∫ d,arrayObservation sw tw Fw d ∂sampleLaw k hc.nonneg n hn)=∫ z,W z ∂area := by
    rw [integral_sampleLaw k hc.nonneg n hn _ (continuous_arrayObservation sw tw Fw hFw.continuous)]
    simp_rw [heW]
    exact integral_torusIter k b W
  have hhint : (∫ d,arrayObservation sh th Fh d ∂sampleLaw k hc.nonneg n hn)=∫ z,H z ∂area := by
    rw [integral_sampleLaw k hc.nonneg n hn _ (continuous_arrayObservation sh th Fh hFh.continuous)]
    simp_rw [heH]
    exact integral_torusIter k b H
  rw [integral_sampleLaw k hc.nonneg n hn F hF,hwint,hhint]
  have hb := actual_fast_bridge_real k hc N r hN hr aw nw Fw ah nh Fh hnw hnh L hFw hFh hlenw hlenh
    hwinw hwinh hW0 hH0 hlog hLM η hη hδ
  exact hbound.trans ((mul_le_mul_of_nonneg_left hb hD).trans_eq (by dsimp only [W,H]; ring))
end StandardMapEntropy

end OAI
