import Mathlib
import OAI.Probability.Perceptron.Pressure.IndexedGibbsPartition

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_indexed_log_recursion {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S→X) (hs : Measurable step)
    (H : X→ℝ) (hH : Measurable H) {C : ℝ} (hC : ∀ x,|H x|≤C)
    (k : ℕ) (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (x : X) :
    (∫ p : IndexedCascadeBase k×IndexedCascadeMarks S k,
      Real.log (∫ l,Real.exp (H (indexedLeafState step k (x,p.2) l))
        ∂indexedLeafProbability k p.1)
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        (indexedCascadeMarksLaw ν k))=
      finiteCascadeLogRecursion ν step k z H x := by
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  let M := (indexedCascadeMarksLaw ν k : Measure (IndexedCascadeMarks S k))
  have hb : ∀ᵐ p ∂B.prod M,IndexedCascadeGood k p.1 :=
    (measurePreserving_fst (μ:=B) (ν:=M)).quasiMeasurePreserving.ae
      (indexedCascadeGood_ae k z hz0 hz1)
  have hr : ∀ᵐ p ∂B.prod M,0<((indexedLeafMeasure k p.1) univ).toReal :=
    (measurePreserving_fst (μ:=B) (ν:=M)).quasiMeasurePreserving.ae
      (indexedLeafMeasure_regular k z hz hz0 hz1)
  have he : (fun p : IndexedCascadeBase k×IndexedCascadeMarks S k=>
      Real.log (∫ l,Real.exp (H (indexedLeafState step k (x,p.2) l))
        ∂indexedLeafProbability k p.1))=ᵐ[B.prod M]
      (fun p=>Real.log (decoratedTerminalTotal step H k (x,indexedCascadeRealize k p)/
        decoratedTerminalTotal step (fun _=>0) k (x,indexedCascadeRealize k p))) := by
    filter_upwards [hb,hr] with p hp hpr
    rw [indexedLeafProbability_terminal_integral ν hs hH k p.1 hp hpr p.2 x]
  have hm : Measurable (fun η : DecoratedCascade S k=>
      Real.log (decoratedTerminalTotal step H k (x,η)/decoratedTerminalTotal step (fun _=>0) k (x,η))) :=
    (((decoratedTerminalTotal_measurable ν step hs hH k z).comp (measurable_const.prodMk measurable_id)).div
      ((decoratedTerminalTotal_measurable ν step hs measurable_const k z).comp
        (measurable_const.prodMk measurable_id))).log
  change (∫ p,Real.log (∫ l,Real.exp (H (indexedLeafState step k (x,p.2) l))
    ∂indexedLeafProbability k p.1) ∂B.prod M)=_
  rw [integral_congr_ae he,←integral_map (indexedCascadeRealize_measurable k).aemeasurable hm.aestronglyMeasurable]
  change (∫ η,Real.log (decoratedTerminalTotal step H k (x,η)/
    decoratedTerminalTotal step (fun _=>0) k (x,η))
    ∂(((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
      (indexedCascadeMarksLaw ν k)).map (indexedCascadeRealize k)))=_
  rw [indexedCascadeRealize_law ν k z]
  exact finiteCascade_terminal_log_recursion_of_fractional ν step hs k z hz hz0 hz1 hH
    (finiteCascadeFractionalIntegrable_of_bounded ν step hs k z hz0 hH hC) x

end SphericalPerceptronFreeEnergy
end

end OAI
