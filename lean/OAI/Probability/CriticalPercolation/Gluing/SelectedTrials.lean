import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.TrialProbability
import OAI.Probability.CriticalPercolation.Gluing.SelectedFresh

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E V : Type*} [Countable E] [Countable V]

lemma selected_no_success_bound (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → Finset V) (F : V → Set E)
    (hd : ∀ U, MeasurableSet[blockSigma X] {ω | d ω=U})
    (hF : ∀ v, F v ⊆ Y) (C : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (K : ℝ)
    (hdis : ∀ σ∈C, (d σ : Set V).Pairwise (fun v w => Disjoint (F v) (F w)))
    (hs : ∀ σ∈C, K ≤ ∑ v∈d σ, (law q).real (allOpen (F v))) :
    (law q).real (C∩{ω | ∀ v∈d ω, ω∉allOpen (F v)}) ≤ Real.exp (-K)*(law q).real C := by
  have hA (U : Finset V) : MeasurableSet[blockSigma Y] (⋂ v∈U, (allOpen (F v))ᶜ) :=
    MeasurableSet.biInter U.countable_toSet (fun v _ =>
      ((blockSigma_mono (hF v)) _ (measurable_allOpen_block (F v))).compl)
  have hh := selected_fresh_bound q X Y hXY d (fun U => ⋂ v∈U, (allOpen (F v))ᶜ)
    hd hA C hC (Real.exp (-K)) (Real.exp_nonneg _)
    (fun σ hσ => disjoint_trials_no_success_le q F (d σ) (hdis σ hσ) K (hs σ hσ))
  simpa only [selectedEvent,Set.mem_iInter,Set.mem_compl_iff] using hh

lemma selected_bad_trial_bound (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → Finset V) (F : V → Set E)
    (A : V → Set (Set E)) (hA : ∀ v, MeasurableSet (A v))
    (hAu : ∀ v, IsUpperSet (A v))
    (hd : ∀ U, MeasurableSet[blockSigma X] {ω | d ω=U})
    (hF : ∀ v, F v ⊆ Y) (C : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (K η lam : ℝ) (hK : 0 ≤ K+1) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hmean : ∀ σ∈C, ∀ v∈d σ, 1-η ≤ (law q).real (A v))
    (hs : ∀ σ∈C, (∑ v∈d σ, (law q).real (allOpen (F v))) ≤ K+1) :
    (law q).real (C∩{ω | ∃ v∈d ω, ω∈allOpen (F v) ∧
      (blockProbability q Y (A v) ω).toReal<1-lam}) ≤
        ((K+1)*η/lam)*(law q).real C := by
  let Bad := fun v => allOpen (F v)∩{σ | (blockProbability q Y (A v) σ).toReal<1-lam}
  have hmB (v : V) : MeasurableSet[blockSigma Y] (Bad v) :=
    ((blockSigma_mono (hF v)) _ (measurable_allOpen_block (F v))).inter
      (measurableSet_lt (measurable_blockProbability q Y (A v) (hA v)).ennreal_toReal
        measurable_const)
  have hb (σ : Set E) (hσ : σ∈C) (v : V) (hv : v∈d σ) : (law q).real (Bad v) ≤ (law q).real (allOpen (F v))*(η/lam) := by
    simpa only [mul_div_assoc] using good_trial_bound q Y (F v) (A v) (hA v) (hAu v)
      η lam hlam (hmean σ hσ v hv)
  have hh := selected_fresh_bound q X Y hXY d (fun U => ⋃ v∈U, Bad v) hd
    (fun U => MeasurableSet.biUnion U.countable_toSet (fun v _ => hmB v))
    C hC ((K+1)*(η/lam)) (mul_nonneg hK (div_nonneg hη hlam.le))
    (fun σ hσ => bad_trial_union_bound q (d σ) Bad (fun v => (law q).real (allOpen (F v)))
      K (η/lam) (div_nonneg hη hlam.le) (fun v hv => hb σ hσ v hv) (hs σ hσ))
  have he : selectedEvent d (fun U => ⋃ v∈U, Bad v)=
      {ω | ∃ v∈d ω, ω∈allOpen (F v) ∧
        (blockProbability q Y (A v) ω).toReal<1-lam} := by
    ext ω
    simp only [selectedEvent, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Bad]
    aesop
  rw [he] at hh
  simpa only [mul_div_assoc] using hh

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
