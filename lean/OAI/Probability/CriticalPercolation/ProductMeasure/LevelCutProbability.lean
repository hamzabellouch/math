import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.BlockIndependence
import OAI.Probability.CriticalPercolation.Gluing.SelectedFresh

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

theorem selected_fresh_lower [Countable I] (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → I) (A : I → Set (Set E))
    (hd : ∀ i, MeasurableSet[blockSigma X] {ω | d ω=i})
    (hA : ∀ i, MeasurableSet[blockSigma Y] (A i))
    (C : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (r : ℝ) (hr : 0 ≤ r) (hb : ∀ σ∈C, r ≤ (law q).real (A (d σ))) :
    r*(law q).real C ≤ (law q).real (C∩selectedEvent d A) := by
  have hmA := measurableSet_selectedEvent d A (fun i => blockSigma_le X _ (hd i))
    (fun i => blockSigma_le Y _ (hA i))
  have hk (σ : Set E) (hσ : σ∈C) :
      ENNReal.ofReal r ≤ blockProbability q X (selectedEvent d A) σ := by
    rw [blockProbability_selected q X Y hXY d A hd hA σ]
    apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
    rw [ENNReal.toReal_ofReal hr]
    exact hb σ hσ
  have hh : ENNReal.ofReal r*law q C ≤ law q (selectedEvent d A∩C) := by
    rw [← setLIntegral_blockProbability q X _ C hmA hC]
    calc
      _ = ∫⁻ _ in C, ENNReal.ofReal r ∂law q := by
        rw [lintegral_const,Measure.restrict_apply_univ]
      _ ≤ _ := setLIntegral_mono' (blockSigma_le X _ hC) hk
  have ht := ENNReal.toReal_mono (measure_ne_top _ _) hh
  simpa only [Set.inter_comm (selectedEvent d A) C,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hr,Measure.real] using ht

lemma law_closedBlock_lower (q : E → unitInterval) (S : Set E) (hS : S.Finite)
    (p : unitInterval) (N : ℕ) (hN : S.ncard ≤ N)
    (hq : ∀ e∈S, (q e : ℝ) ≤ p) :
    (1-(p : ℝ))^N ≤ (law q).real (closedBlock S) := by
  have hp0 : 0 ≤ 1-(p : ℝ) := sub_nonneg.mpr p.2.2
  have hp1 : 1-(p : ℝ) ≤ 1 := by linarith [p.2.1]
  rw [measureReal_def,law_closedBlock q S hS,ENNReal.toReal_prod]
  calc
    _ ≤ (1-(p : ℝ))^S.ncard := pow_le_pow_of_le_one hp0 hp1 hN
    _ = ∏ e∈hS.toFinset, (1-(p : ℝ)) := by simp [Set.ncard_eq_toFinset_card S hS]
    _ ≤ _ := by
      apply Finset.prod_le_prod₀
      · intro e he; exact hp0
      · intro e he
        change 1-(p : ℝ) ≤ (bitMeasure (q e)).real {False}
        rw [bitMeasure_real_singleton]
        simpa only [bitWeight,ite_false] using sub_le_sub_left (hq e (hS.mem_toFinset.mp he)) 1

lemma exists_level_small (μ : Measure (Set E)) [IsProbabilityMeasure μ]
    (J : Finset I) (hJ : J.Nonempty) (C M : I → Set (Set E))
    (hM : ∀ i∈J, MeasurableSet (M i))
    (hdis : (J : Set I).PairwiseDisjoint M) (c : ℝ) (hc : 0 < c)
    (hb : ∀ i∈J, c*μ.real (C i) ≤ μ.real (M i)) :
    ∃ i∈J, μ.real (C i) ≤ 1/((J.card : ℝ)*c) := by
  have hsum : (∑ i∈J, μ.real (M i)) ≤ 1 := by
    rw [← measureReal_biUnion_finset hdis hM]
    exact measureReal_le_one
  have hcard : 0 < (J.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hJ
  by_contra h
  push Not at h
  have hs : (∑ i∈J, 1/(J.card : ℝ)) < ∑ i∈J, μ.real (M i) := by
    apply Finset.sum_lt_sum_of_nonempty hJ
    intro i hi
    have hh := mul_lt_mul_of_pos_left (h i hi) hc
    have he : c*(1/((J.card : ℝ)*c))=1/(J.card : ℝ) := by field_simp
    rw [he] at hh
    exact hh.trans_le (hb i hi)
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have he : (J.card : ℝ)*(1/(J.card : ℝ))=1 := by field_simp
  rw [he] at hs
  exact (not_lt_of_ge hsum) hs

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
