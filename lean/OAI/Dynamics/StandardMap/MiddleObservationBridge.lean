import OAI.Dynamics.StandardMap.BridgeAveraging

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def shortfallObservation (k : ℝ) {R : ℕ} (a : Fin R → ℤ) (n : Fin R → ℕ)
    (F : (Fin R → ℝ) → ℝ) (z : Torus) : ℝ := F (fun j => torusShortfall k z (a j) (n j))
lemma shortfallObservation_shift (k : ℝ) {R : ℕ} (a : Fin R → ℤ) (n : Fin R → ℕ)
    (F : (Fin R → ℝ) → ℝ) (b : ℤ) (z : Torus) :
    shortfallObservation k a n F (torusIter k b z)=shortfallObservation k (fun j => a j+b) n F z := by
  unfold shortfallObservation
  congr 1
  funext j
  exact torusShortfall_shift k z (a j) b (n j)
lemma middle_observation_product (k : ℝ) (hc : BridgeScalarControl k)
    (N r i : ℕ) (hN : 100 ≤ N) (hi : i∈bridgeMiddle N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
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
    (∫⁻ z in (torusIter k (i:ℤ) ⁻¹' middlePrefixEvent k (N-i) i) ∩
      {z | h < shortfallObservation k ah nh Fh z},
      ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area) ≤ middleBridgeConstant*((∫⁻ z, ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area)+
        ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*
          area {z | h/2 < shortfallObservation k ah nh Fh z} := by
  have hiB := bridgeMiddle_bounds N i hN hi
  let Wi := shortfallObservation k (fun j => aw j-(i:ℤ)) nw Fw
  let Hi := shortfallObservation k (fun j => ah j-(i:ℤ)) nh Fh
  have hWi : Continuous Wi := continuous_shortfall_observation k hc.nonneg _ _ _ hFw.continuous
  have hHi : Continuous Hi := continuous_shortfall_observation k hc.nonneg _ _ _ hFh.continuous
  have hWiS (z : Torus) : Wi (torusIter k (i:ℤ) z)=shortfallObservation k aw nw Fw z := by
    dsimp only [Wi]
    rw [shortfallObservation_shift]
    simp only [sub_add_cancel]
  have hHiS (z : Torus) : Hi (torusIter k (i:ℤ) z)=shortfallObservation k ah nh Fh z := by
    dsimp only [Hi]
    rw [shortfallObservation_shift]
    simp only [sub_add_cancel]
  have hWi0 (z : Torus) : 0 ≤ Wi z := by
    have hh := hW0 (torusIter k (-(i:ℤ)) z)
    rw [← hWiS,← torusIter_add,add_neg_cancel,torusIter_zero] at hh
    exact hh
  have hMp : 0 < growthBase k := by linarith [growthBase_ge_four k hc.nonneg]
  have hh := actual_middle_prefix_product k hc (N-i) i hiB.2.1 hiB.1 Wi Hi hWi hHi hWi0
    h (growthBase k^(-(1/10:ℝ)*(N:ℝ))) (Real.rpow_nonneg hMp.le _) hδ
    (by
      intro z w hd
      apply endpoint_shortfall_observation k hc.nonneg _ nw hnw Fw L hFw (-(i:ℤ)) r N i
        hlenw _ hN hr hiB.2.2.1 (by omega) hlog hLM z w hd
      intro j l hl hln
      simpa only [sub_neg_eq_add,sub_add_cancel,show aw j-(i:ℤ)+(l:ℤ)-1+(i:ℤ)=aw j+(l:ℤ)-1 by ring] using hwinw j l hl hln)
    (by
      intro z w hd
      apply endpoint_shortfall_observation k hc.nonneg _ nh hnh Fh L hFh ((N-i:ℕ):ℤ) r N (N-i)
        hlenh _ hN hr hiB.2.2.2.1 (by omega) hlog hLM z w hd
      intro j l hl hln
      have he : ah j-(i:ℤ)+(l:ℤ)-1-((N-i:ℕ):ℤ)=ah j+(l:ℤ)-1-(N:ℤ) := by omega
      simpa only [he] using hwinh j l hl hln)
  have hmp := measurePreserving_torusIter k (i:ℤ)
  have hleft := hmp.setLIntegral_comp_preimage (s := middlePrefixEvent k (N-i) i ∩ {z | h < Hi z})
    ((measurableSet_middlePrefixEvent k (N-i) i).inter (isOpen_lt continuous_const hHi).measurableSet)
    (hWi.measurable.ennreal_ofReal)
  have hwint := hmp.lintegral_comp (hWi.measurable.ennreal_ofReal)
  rw [← hwint] at hh
  simp only [hWiS] at hh
  have hm : area {z | h/2 < Hi z}=area {z | h/2 < shortfallObservation k ah nh Fh z} := by
    symm
    simpa only [Set.preimage_ofPred_eq,hHiS] using hmp.measure_preimage (s := {z | h/2 < Hi z}) (show MeasurableSet {z | h/2 < Hi z} from (isOpen_lt continuous_const hHi).measurableSet).nullMeasurableSet
  rw [hm] at hh
  simpa only [Set.preimage_inter,Set.preimage_ofPred_eq,hWiS,hHiS] using hleft.trans_le hh
end StandardMapEntropy

end OAI
