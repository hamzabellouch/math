import Mathlib
import OAI.Probability.Perceptron.Variational.CouplingKernel

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavity_indexed_log_recursion_fractional {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S→X) (hs : Measurable step)
    (H : X→ℝ) (hH : Measurable H)
    (k : ℕ) (z : Fin k→ℝ) (hfrac : finiteCascadeFractionalIntegrable ν step H k z) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
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
    hfrac x

def indexedRootTerminalPartition {X S Y : Type} [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace Y]
    (step : X×S→X) (H : X→ℝ) (root : Y→X) (k : ℕ)
    (p : Y×(IndexedCascadeBase k×IndexedCascadeMarks S k)) : ℝ :=
  ∫ l,Real.exp (H (indexedLeafState step k (root p.1,p.2.2) l)) ∂indexedLeafProbability k p.2.1

lemma indexedRootTerminalPartition_measurable {X S Y : Type} [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace Y]
    (step : X×S→X) (hs : Measurable step) (H : X→ℝ) (hH : Measurable H)
    (root : Y→X) (hr : Measurable root) (k : ℕ) :
    Measurable (indexedRootTerminalPartition step H root k) := by
  let κ : Kernel (Y×(IndexedCascadeBase k×IndexedCascadeMarks S k)) (IndexedLeaf k):=
    (indexedLeafKernel k).comap (fun p=>p.2.1) measurable_snd.fst
  have hp : Measurable (fun p : (Y×(IndexedCascadeBase k×IndexedCascadeMarks S k))×IndexedLeaf k=>
      ((root p.1.1,p.1.2.2),p.2)) :=
    ((hr.comp measurable_fst.fst).prodMk measurable_fst.snd.snd).prodMk measurable_snd
  have h := (hH.comp ((indexedLeafState_measurable hs k).comp hp)).exp
  exact (h.stronglyMeasurable.integral_kernel_prod_right (κ:=κ)
    (f:=fun p l=>Real.exp (H (indexedLeafState step k (root p.1,p.2.2) l)))).measurable

lemma indexed_root_log_fractional {X S Y : Type} [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace Y]
    [Nonempty S] (ν : ProbabilityMeasure S) (ρ : Measure Y) [IsProbabilityMeasure ρ]
    (step : X×S→X) (hs : Measurable step) (H : X→ℝ) (hH : Measurable H)
    (root : Y→X) (k : ℕ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (hfrac : finiteCascadeFractionalIntegrable ν step H k z)
    (hi : Integrable (fun p=>Real.log (indexedRootTerminalPartition step H root k p))
      (ρ.prod ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod (indexedCascadeMarksLaw ν k)))) :
    (∫ p,Real.log (indexedRootTerminalPartition step H root k p)
      ∂ρ.prod ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod (indexedCascadeMarksLaw ν k)))=
      ∫ y,finiteCascadeLogRecursion ν step k z H (root y) ∂ρ := by
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun y=>cavity_indexed_log_recursion_fractional ν step hs H hH k z hfrac hz hz0 hz1 (root y)

end SphericalPerceptronFreeEnergy
end

end OAI
