import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.ProductConditioning

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

lemma block_event_disjoint_forceOn (X Y : Set E) (hXY : Disjoint X Y)
    (A : Set (Set E)) (hA : MeasurableSet[blockSigma Y] A) (σ ω : Set E) :
    forceOn X σ ω∈A ↔ ω∈A := by
  have he : forceOn Y (forceOn X σ ω) ω=ω := by
    ext e
    by_cases heY : e∈Y
    · have heX : e∉X := fun h => Set.disjoint_left.mp hXY h heY
      simp only [mem_forceOn,ite_eq_left heY,ite_eq_right heX]
    · simp only [mem_forceOn,ite_eq_right heY]
  have hh := block_event_forceOn Y A hA (forceOn X σ ω) ω
  rw [he] at hh
  exact hh.symm

def selectedEvent (d : Set E → I) (A : I → Set (Set E)) : Set (Set E) :=
  {ω | ω∈A (d ω)}

lemma selectedEvent_eq_iUnion (d : Set E → I) (A : I → Set (Set E)) :
    selectedEvent d A=⋃ i, ({ω | d ω=i}∩A i) := by
  ext ω
  simp only [selectedEvent,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
  exact ⟨fun h => ⟨d ω,rfl,h⟩,fun ⟨i,hi,h⟩ => hi.symm ▸ h⟩

lemma measurableSet_selectedEvent [Countable I] (d : Set E → I)
    (A : I → Set (Set E)) (hd : ∀ i, MeasurableSet {ω | d ω=i})
    (hA : ∀ i, MeasurableSet (A i)) : MeasurableSet (selectedEvent d A) := by
  rw [selectedEvent_eq_iUnion]
  exact MeasurableSet.iUnion (fun i => (hd i).inter (hA i))

theorem blockProbability_selected (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → I) (A : I → Set (Set E))
    (hd : ∀ i, MeasurableSet[blockSigma X] {ω | d ω=i})
    (hA : ∀ i, MeasurableSet[blockSigma Y] (A i)) (σ : Set E) :
    blockProbability q X (selectedEvent d A) σ=law q (A (d σ)) := by
  unfold blockProbability
  congr 1
  ext ω
  change forceOn X σ ω∈A (d (forceOn X σ ω)) ↔ ω∈A (d σ)
  have hh : d (forceOn X σ ω)=d σ :=
    (block_event_forceOn X {τ | d τ=d σ} (hd _) σ ω).mpr rfl
  rw [hh]
  exact block_event_disjoint_forceOn X Y hXY (A (d σ)) (hA _) σ ω

theorem selected_fresh_bound [Countable I] (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → I) (A : I → Set (Set E))
    (hd : ∀ i, MeasurableSet[blockSigma X] {ω | d ω=i})
    (hA : ∀ i, MeasurableSet[blockSigma Y] (A i))
    (C : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (r : ℝ) (hr : 0 ≤ r) (hb : ∀ σ∈C, (law q).real (A (d σ)) ≤ r) :
    (law q).real (C∩selectedEvent d A) ≤ r*(law q).real C := by
  have hmA := measurableSet_selectedEvent d A (fun i => blockSigma_le X _ (hd i))
    (fun i => blockSigma_le Y _ (hA i))
  have hk (σ : Set E) (hσ : σ∈C) :
      blockProbability q X (selectedEvent d A) σ ≤ ENNReal.ofReal r := by
    rw [blockProbability_selected q X Y hXY d A hd hA σ]
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hr]
    exact hb σ hσ
  have hh : law q (selectedEvent d A∩C) ≤ ENNReal.ofReal r*law q C := by
    rw [← setLIntegral_blockProbability q X _ C hmA hC]
    calc
      (∫⁻ σ in C, blockProbability q X (selectedEvent d A) σ ∂law q) ≤
          ∫⁻ _ in C, ENNReal.ofReal r ∂law q :=
        setLIntegral_mono' (blockSigma_le X _ hC) hk
      _ = _ := by rw [lintegral_const,Measure.restrict_apply_univ]
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (measure_ne_top _ _)) hh
  simpa only [Set.inter_comm (selectedEvent d A) C,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hr,Measure.real] using ht

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
