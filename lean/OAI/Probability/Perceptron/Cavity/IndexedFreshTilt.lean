import Mathlib
import OAI.Probability.Perceptron.Pressure.IndexedGibbsPartition
import OAI.Probability.Perceptron.Cascade.CascadeIndependentTilt

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

lemma indexedLeaf_tilt_terminal_ratio {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {step : X×S→X} (hs : Measurable step)
    {H G : X→ℝ} (hH : Measurable H) (hG : Measurable G)
    (n : ℕ) (b : IndexedCascadeBase n) (hb : IndexedCascadeGood n b)
    (hb' : 0<((indexedLeafMeasure n b) univ).toReal) (m : IndexedCascadeMarks S n) (x : X) :
    tiltMean (indexedLeafProbability n b)
      (fun l => G (indexedLeafState step n (x,m) l))
      (fun l => Real.exp (H (indexedLeafState step n (x,m) l))) 1 =
    decoratedTerminalTotal step (fun x => H x+G x) n (x,indexedCascadeRealize n (b,m)) /
      decoratedTerminalTotal step G n (x,indexedCascadeRealize n (b,m)) := by
  have hzero := indexedLeafProbability_terminal_integral ν hs (H := fun _ => 0)
    measurable_const n b hb hb' m x
  simp only [Real.exp_zero,integral_const,probReal_univ,one_smul] at hzero
  have hne : decoratedTerminalTotal step (fun _ => 0) n (x,indexedCascadeRealize n (b,m))≠0 := by
    intro hz
    rw [hz,div_zero] at hzero
    exact one_ne_zero hzero
  unfold tiltMean tiltIntegral tiltPartition
  simp only [one_mul]
  have he : (fun l => Real.exp (G (indexedLeafState step n (x,m) l)) *
      Real.exp (H (indexedLeafState step n (x,m) l))) =
      (fun l => Real.exp ((fun y => H y+G y) (indexedLeafState step n (x,m) l))) := by
    funext l
    rw [Real.exp_add,mul_comm]
  rw [he,indexedLeafProbability_terminal_integral ν hs (H := fun a => H a+G a) (hH.add hG) n b hb hb' m x,
    indexedLeafProbability_terminal_integral ν hs hG n b hb hb' m x]
  field_simp

theorem indexed_independent_fresh_log {X Y S T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace T]
    [Nonempty S] [Nonempty T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    {H : X→ℝ} {G : Y→ℝ} (hH : Measurable H) (hG : Measurable G)
    (hIH : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hIG : finiteCascadeFractionalIntegrable ρ step₂ G n z) (x : X) (y : Y) :
    (∫ p, Real.log (tiltMean (indexedLeafProbability n p.1)
      (fun l => G (indexedLeafState
        (fun a : (X×Y)×(S×T) => (step₁ (a.1.1,a.2.1),step₂ (a.1.2,a.2.2))) n ((x,y),p.2) l).2)
      (fun l => Real.exp (H (indexedLeafState
        (fun a : (X×Y)×(S×T) => (step₁ (a.1.1,a.2.1),step₂ (a.1.2,a.2.2))) n ((x,y),p.2) l).1)) 1)
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw (productMarkLaw ν ρ) n)) =
      finiteCascadeLogRecursion ν step₁ n z H x := by
  let step : (X×Y)×(S×T)→X×Y := fun a => (step₁ (a.1.1,a.2.1),step₂ (a.1.2,a.2.2))
  have hs : Measurable step := by fun_prop
  let B := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n))
  let M := (indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n))
  have hb : ∀ᵐ p ∂B.prod M, IndexedCascadeGood n p.1 :=
    (measurePreserving_fst (μ := B) (ν := M)).quasiMeasurePreserving.ae
      (indexedCascadeGood_ae n z hz0 hz1)
  have hb' : ∀ᵐ p ∂B.prod M, 0<((indexedLeafMeasure n p.1) univ).toReal :=
    (measurePreserving_fst (μ := B) (ν := M)).quasiMeasurePreserving.ae
      (indexedLeafMeasure_regular n z hz hz0 hz1)
  have he : (fun p : IndexedCascadeBase n×IndexedCascadeMarks (S×T) n =>
      Real.log (tiltMean (indexedLeafProbability n p.1)
        (fun l => G (indexedLeafState step n ((x,y),p.2) l).2)
        (fun l => Real.exp (H (indexedLeafState step n ((x,y),p.2) l).1)) 1)) =ᵐ[B.prod M]
    (fun p => Real.log (decoratedTerminalTotal step (fun a => H a.1+G a.2) n
      ((x,y),indexedCascadeRealize n p) /
        decoratedTerminalTotal step (fun a => G a.2) n ((x,y),indexedCascadeRealize n p))) := by
    filter_upwards [hb,hb'] with p hp hp'
    congr 1
    exact indexedLeaf_tilt_terminal_ratio (productMarkLaw ν ρ) hs
      (hH.comp measurable_fst) (hG.comp measurable_snd) n p.1 hp hp' p.2 (x,y)
  change (∫ p, Real.log (tiltMean (indexedLeafProbability n p.1)
        (fun l => G (indexedLeafState step n ((x,y),p.2) l).2)
        (fun l => Real.exp (H (indexedLeafState step n ((x,y),p.2) l).1)) 1) ∂B.prod M)=_
  rw [integral_congr_ae he]
  have hm : Measurable (fun η : DecoratedCascade (S×T) n =>
      Real.log (decoratedTerminalTotal step (fun a => H a.1+G a.2) n ((x,y),η) /
        decoratedTerminalTotal step (fun a => G a.2) n ((x,y),η))) := by
    exact (((decoratedTerminalTotal_measurable (productMarkLaw ν ρ) step hs
      ((hH.comp measurable_fst).add (hG.comp measurable_snd)) n z).comp (by fun_prop)).div
      ((decoratedTerminalTotal_measurable (productMarkLaw ν ρ) step hs
        (hG.comp measurable_snd) n z).comp (by fun_prop))).log
  rw [← integral_map (indexedCascadeRealize_measurable n).aemeasurable hm.aestronglyMeasurable,
    indexedCascadeRealize_law (productMarkLaw ν ρ) n z]
  exact finiteCascade_independent_tilt_log ν ρ step₁ step₂ hs₁ hs₂ n z hz hz0 hz1 hH hG hIH hIG x y

end SphericalPerceptronFreeEnergy
end

end OAI
