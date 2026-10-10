import OAI.NumberTheory.DukePrimeDegree.Entropy.FiniteLabelEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalSigmaLimit

namespace OAI

/-! # Entropy limits for decreasing positive-mass conditioning cells -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_restriction_real {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (A B : Set Y) (hB : MeasurableSet B) :
    ((anchorNormalize ν A).restrict A).real B = ν.real (B ∩ A) / ν.real A := by
  rw [measureReal_def,Measure.restrict_apply hB,anchorNormalize,Measure.smul_apply]
  simp only [smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,measureReal_def,
    div_eq_mul_inv,mul_comm]

theorem normalized_restriction_probability_tendsto {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν]
    (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n)) (hdec : Antitone A)
    (hpos : ν (⋂ n, A n) ≠ 0) (B : Set Y) (hB : MeasurableSet B) :
    Tendsto (fun n => ((anchorNormalize ν (A n)).restrict (A n)).real B) atTop
      (𝓝 (((anchorNormalize ν (⋂ n, A n)).restrict (⋂ n, A n)).real B)) := by
  have hden := tendsto_measure_iInter_atTop (μ := ν) (fun n => (hA n).nullMeasurableSet)
    hdec ⟨0,measure_ne_top _ _⟩
  have hnum := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (hB.inter (hA n)).nullMeasurableSet)
    (show Antitone (fun n => B ∩ A n) from fun n m hnm => inter_subset_inter subset_rfl (hdec hnm))
    ⟨0,measure_ne_top _ _⟩
  have he : (⋂ n, B ∩ A n) = B ∩ ⋂ n, A n := by
    ext y
    simp only [mem_iInter,mem_inter_iff]
    exact ⟨fun h => ⟨(h 0).1, fun i => (h i).2⟩,fun h i => ⟨h.1,h.2 i⟩⟩
  rw [he] at hnum
  have htden := (ENNReal.tendsto_toReal (measure_ne_top ν (⋂ n, A n))).comp hden
  have htnum := (ENNReal.tendsto_toReal (measure_ne_top ν (B ∩ ⋂ n, A n))).comp hnum
  have hd : ν.real (⋂ n, A n) ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hpos,measure_ne_top _ _⟩
  have H := htnum.div htden hd
  change Tendsto (fun n => (ν (B ∩ A n)).toReal / (ν (A n)).toReal) atTop
    (𝓝 ((ν (B ∩ ⋂ n, A n)).toReal / (ν (⋂ n, A n)).toReal)) at H
  simpa only [Function.comp_def,normalized_restriction_real ν _ B hB,
    measureReal_def] using H

theorem normalized_restriction_entropy_tendsto {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (ν : Measure Y) [IsFiniteMeasure ν]
    (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n)) (hdec : Antitone A)
    (hpos : ν (⋂ n, A n) ≠ 0) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) :
    Tendsto (fun n => observationEntropy ((anchorNormalize ν (A n)).restrict (A n)) P) atTop
      (𝓝 (observationEntropy ((anchorNormalize ν (⋂ n, A n)).restrict (⋂ n, A n)) P)) := by
  have H := continuous_finiteShannon.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr (fun a => normalized_restriction_probability_tendsto
      ν A hA hdec hpos {y | P y=a} (hP a)))
  simpa only [Function.comp_def,observationEntropy] using H

end DukePrimeDegree

end

end OAI
