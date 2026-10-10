import Mathlib
import OAI.Probability.Perceptron.Variational.ContactGGRate
import OAI.Probability.Perceptron.Variational.IndexedMarkProduct
import OAI.Probability.Perceptron.Variational.TiltedPathProduct
import OAI.Probability.Perceptron.Pressure.IndexedTerminalGibbs

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X Y S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace S] [MeasurableSpace T]

lemma cascadeTiltedStep_parallel (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : ∀ i, 0<z i) (H : X→ℝ) (G : Y→ℝ)
    (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z) (i : Fin n) :
    tiltedStateStep (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) (z i)
      (finiteCascadeShifts (productMarkLaw ν ρ)
        (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n z
          (fun x => H x.1+G x.2) i) =
      tiltedStateStep ν step₁ (z i) (finiteCascadeShifts ν step₁ n z H i) ∥ₖ
        tiltedStateStep ρ step₂ (z i) (finiteCascadeShifts ρ step₂ n z G i) := by
  have he := fun p => finiteCascadeShifts_add_product ν ρ step₁ step₂ n z hz hHI hGI i p
  rw [funext he]
  exact tiltedStateStep_parallel ν ρ step₁ step₂ hs₁ hs₂ (z i) _ _
    (finiteCascadeShifts_measurable ν step₁ hs₁ n z hH i)
    (finiteCascadeShifts_measurable ρ step₂ hs₂ n z hG i)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step₁ n z (fun i => (hz i).ne') H hHI i x).1)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ρ step₂ n z (fun i => (hz i).ne') G hGI i x).1)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step₁ n z (fun i => (hz i).ne') H hHI i x).2)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ρ step₂ n z (fun i => (hz i).ne') G hGI i x).2)

lemma cascadeTiltedStep_markov (ν : ProbabilityMeasure S) (step : X×S→X)
    (hs : Measurable step) (n : ℕ) (z : Fin n→ℝ) (hz : ∀ i, 0<z i)
    (H : X→ℝ) (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z)
    (i : Fin n) :
    IsMarkovKernel (tiltedStateStep ν step (z i) (finiteCascadeShifts ν step n z H i)) :=
  tiltedStateStep_markov ν step hs (z i) _ (finiteCascadeShifts_measurable ν step hs n z hH i)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz i).ne') H hI i x).1)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz i).ne') H hI i x).2)

lemma pathCorrelation_one (n : ℕ) (κ : Fin n→Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (d : Fin (n+1)) (x : X) : pathCorrelation n κ (fun _ => 1) d x=1 := by
  have := pathPairKernel_markov n κ hκ d
  simp [pathCorrelation]

lemma indexed_terminal_product_pair_integral [Nonempty S] [Nonempty T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z) (x : X) (y : Y) (d : Fin (n+1))
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ x, |f x|≤C) (hgB : ∀ y, |g y|≤D) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    let term := fun x : X×Y => H x.1+G x.2
    (∫ p, (∫ l : IndexedLeaf n×IndexedLeaf n,
        (f (indexedLeafState st n ((x,y),p.2) l.1).1*g (indexedLeafState st n ((x,y),p.2) l.1).2)*
        (f (indexedLeafState st n ((x,y),p.2) l.2).1*g (indexedLeafState st n ((x,y),p.2) l.2).2)
      ∂((tiltLaw (indexedLeafProbability n p.1)
          (fun a => term (indexedLeafState st n ((x,y),p.2) a)) 1).prod
        (tiltLaw (indexedLeafProbability n p.1)
          (fun a => term (indexedLeafState st n ((x,y),p.2) a)) 1)).restrict
          {l | indexedCommonDepth n l.1 l.2=d})
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n))) =
      (twoVisitMass n z d).toReal *
        (pathCorrelation n (fun i => tiltedStateStep ν step₁ (z i) (finiteCascadeShifts ν step₁ n z H i)) f d x *
          pathCorrelation n (fun i => tiltedStateStep ρ step₂ (z i) (finiteCascadeShifts ρ step₂ n z G i)) g d y) := by
  dsimp only
  have hfg : Measurable (fun p : X×Y => f p.1*g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hB : ∀ p : X×Y, |f p.1*g p.2|≤C*D := fun p => by
    rw [abs_mul]; exact mul_le_mul (hfB p.1) (hgB p.2) (abs_nonneg _) hC
  have he := indexed_terminal_pair_integral (productMarkLaw ν ρ)
    (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) (by fun_prop)
    n z hz hz0 hz1 (fun p : X×Y => H p.1+G p.2)
    (show Measurable (fun p : X×Y => H p.1+G p.2) from
      (hH.comp measurable_fst).add (hG.comp measurable_snd))
    (finiteCascadeFractionalIntegrable_add_product ν ρ step₁ step₂ n z hz0 hHI hGI)
    (x,y) d (fun p : X×Y => f p.1*g p.2) hfg (C*D) (mul_nonneg hC hD) hB
  refine he.trans ?_
  simp_rw [cascadeTiltedStep_parallel ν ρ step₁ step₂ hs₁ hs₂ n z hz0 H G hH hG hHI hGI]
  rw [pathCorrelation_parallel n _ _
    (cascadeTiltedStep_markov ν step₁ hs₁ n z hz0 H hH hHI)
    (cascadeTiltedStep_markov ρ step₂ hs₂ n z hz0 G hG hGI) f g hf hg C D hC hD hfB hgB]

def indexedTerminalBaseKernel (n : ℕ) :
    Kernel (IndexedCascadeBase n×IndexedCascadeMarks S n) (IndexedLeaf n) :=
  (indexedLeafKernel n).comap Prod.fst measurable_fst
instance (n : ℕ) : IsMarkovKernel (indexedTerminalBaseKernel (S:=S) n) := by
  unfold indexedTerminalBaseKernel
  infer_instance

def indexedTerminalEnergy (step : X×S→X) (n : ℕ) (H : X→ℝ) (x : X)
    (p : IndexedCascadeBase n×IndexedCascadeMarks S n) (l : IndexedLeaf n) : ℝ :=
  H (indexedLeafState step n (x,p.2) l)

lemma indexedTerminalEnergy_measurable (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (x : X) :
    Measurable (Function.uncurry (indexedTerminalEnergy step n H x)) :=
  hH.comp ((indexedLeafState_measurable hs n).comp
    ((measurable_const.prodMk measurable_fst.snd).prodMk measurable_snd))

def indexedTerminalPairMean (step : X×S→X) (n : ℕ) (H : X→ℝ) (x : X)
    (d : Fin (n+1)) (f : X→ℝ) (p : IndexedCascadeBase n×IndexedCascadeMarks S n) : ℝ :=
  let κ := gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H x)
  ∫ l : IndexedLeaf n×IndexedLeaf n,
    (if indexedCommonDepth n l.1 l.2=d then
      f (indexedLeafState step n (x,p.2) l.1)*f (indexedLeafState step n (x,p.2) l.2) else 0)
      ∂(κ p).prod (κ p)

lemma indexedTerminalPairMean_measurable (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (x : X) (d : Fin (n+1))
    (f : X→ℝ) (hf : Measurable f) :
    Measurable (indexedTerminalPairMean step n H x d f) := by
  let κ := gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H x)
  have hm (j : IndexedLeaf n×IndexedLeaf n→IndexedLeaf n) (hj : Measurable j) :
      Measurable (fun p : (IndexedCascadeBase n×IndexedCascadeMarks S n)×(IndexedLeaf n×IndexedLeaf n) =>
        f (indexedLeafState step n (x,p.1.2) (j p.2))) :=
    hf.comp ((indexedLeafState_measurable hs n).comp
      ((measurable_const.prodMk measurable_fst.snd).prodMk (hj.comp measurable_snd)))
  have hcond : MeasurableSet {p : (IndexedCascadeBase n×IndexedCascadeMarks S n)×(IndexedLeaf n×IndexedLeaf n) |
      indexedCommonDepth n p.2.1 p.2.2=d} :=
    ((Set.to_countable {l : IndexedLeaf n×IndexedLeaf n | indexedCommonDepth n l.1 l.2=d}).measurableSet).preimage measurable_snd
  have : IsMarkovKernel κ := gibbsProbabilityKernel_markov _ _
    (indexedTerminalEnergy_measurable step hs n H hH x)
  let F : (IndexedCascadeBase n×IndexedCascadeMarks S n)×(IndexedLeaf n×IndexedLeaf n)→ℝ :=
    fun p => if indexedCommonDepth n p.2.1 p.2.2=d then
      f (indexedLeafState step n (x,p.1.2) p.2.1)*f (indexedLeafState step n (x,p.1.2) p.2.2) else 0
  have hF : Measurable F :=
    Measurable.ite hcond ((hm Prod.fst measurable_fst).mul (hm Prod.snd measurable_snd)) measurable_const
  have hm' : Measurable (fun p => ∫ l, F (p,l) ∂(κ×ₖκ) p) :=
    (hF.stronglyMeasurable.integral_kernel_prod_right').measurable
  unfold indexedTerminalPairMean
  simpa only [F,κ, Kernel.prod_apply] using hm'

lemma indexedTerminalPairMean_eq (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (x : X) (d : Fin (n+1)) (f : X→ℝ)
    (p : IndexedCascadeBase n×IndexedCascadeMarks S n)
    (hi : Integrable (fun l => Real.exp (H (indexedLeafState step n (x,p.2) l))) (indexedLeafProbability n p.1)) :
    indexedTerminalPairMean step n H x d f p =
      ∫ l : IndexedLeaf n×IndexedLeaf n,
        f (indexedLeafState step n (x,p.2) l.1)*f (indexedLeafState step n (x,p.2) l.2)
      ∂((tiltLaw (indexedLeafProbability n p.1) (indexedTerminalEnergy step n H x p) 1).prod
        (tiltLaw (indexedLeafProbability n p.1) (indexedTerminalEnergy step n H x p) 1)).restrict
          {l | indexedCommonDepth n l.1 l.2=d} := by
  unfold indexedTerminalPairMean
  dsimp only
  rw [gibbsProbabilityKernel_of_integrable (indexedTerminalBaseKernel n) _ (indexedTerminalEnergy_measurable step hs n H hH x) p hi]
  simpa only [Set.indicator_apply,Set.mem_ofPred_eq,indexedTerminalBaseKernel,Kernel.comap_apply,indexedLeafKernel,Kernel.coe_mk] using
    (integral_indicator (f:=fun l : IndexedLeaf n×IndexedLeaf n =>
      f (indexedLeafState step n (x,p.2) l.1)*f (indexedLeafState step n (x,p.2) l.2))
      (μ:=((tiltLaw (indexedLeafProbability n p.1) (indexedTerminalEnergy step n H x p) 1).prod
        (tiltLaw (indexedLeafProbability n p.1) (indexedTerminalEnergy step n H x p) 1)))
      ((Set.to_countable {l : IndexedLeaf n×IndexedLeaf n | indexedCommonDepth n l.1 l.2=d}).measurableSet))

lemma indexedTerminalPairMean_integral [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S→X)
    (hs : Measurable step) (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (H : X→ℝ) (hH : Measurable H)
    (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X) (d : Fin (n+1))
    (f : X→ℝ) (hf : Measurable f) (C : ℝ) (hC : 0≤C) (hfB : ∀ y, |f y|≤C) :
    (∫ p, indexedTerminalPairMean step n H x d f p
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      (twoVisitMass n z d).toReal * pathCorrelation n
        (fun i => tiltedStateStep ν step (z i) (finiteCascadeShifts ν step n z H i)) f d x := by
  rw [←indexed_terminal_pair_integral ν step hs n z hz hz0 hz1 H hH hI x d f hf C hC hfB]
  apply integral_congr_ae
  filter_upwards [indexed_terminal_exp_integrable_ae ν step hs n z hz hz0 hz1 H hH hI x] with p hp
  exact indexedTerminalPairMean_eq step hs n H hH x d f p hp

lemma indexedTerminalPairMean_bound (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (x : X) (d : Fin (n+1)) (f : X→ℝ)
    (C : ℝ) (hC : 0≤C) (hB : ∀ x, |f x|≤C)
    (p : IndexedCascadeBase n×IndexedCascadeMarks S n) :
    |indexedTerminalPairMean step n H x d f p|≤C^2 := by
  have := gibbsProbabilityKernel_markov (indexedTerminalBaseKernel n)
    (indexedTerminalEnergy step n H x) (indexedTerminalEnergy_measurable step hs n H hH x)
  have hb : ∀ l : IndexedLeaf n×IndexedLeaf n,
      ‖(if indexedCommonDepth n l.1 l.2=d then
        f (indexedLeafState step n (x,p.2) l.1)*f (indexedLeafState step n (x,p.2) l.2) else 0)‖≤C^2 := by
    intro l
    split_ifs
    · rw [Real.norm_eq_abs,abs_mul,pow_two]
      exact mul_le_mul (hB _) (hB _) (abs_nonneg _) hC
    · simp only [norm_zero]
      positivity
  simpa [indexedTerminalPairMean] using norm_integral_le_of_norm_le_const
    (μ:=(gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H x) p).prod
      (gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H x) p))
    (Filter.Eventually.of_forall hb)

variable [Nonempty S] [Nonempty T]

lemma indexedTerminalPairMean_independent_arrays
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z) (x : X) (y : Y) (d : Fin (n+1))
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ x, |f x|≤C) (hgB : ∀ y, |g y|≤D) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    (∫ p, indexedTerminalPairMean st n (fun p => H p.1+G p.2) (x,y) d
      (fun p => f p.1*g p.2) (p.1,indexedMarksZip n p.2)
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
          (indexedCascadeMarksLaw ρ n))) =
      (twoVisitMass n z d).toReal *
        (pathCorrelation n (fun i => tiltedStateStep ν step₁ (z i) (finiteCascadeShifts ν step₁ n z H i)) f d x *
          pathCorrelation n (fun i => tiltedStateStep ρ step₂ (z i) (finiteCascadeShifts ρ step₂ n z G i)) g d y) := by
  dsimp only
  let st : (X×Y)×(S×T)→X×Y := fun p => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
  have hs : Measurable st := by fun_prop
  let B := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n))
  let M := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
    (indexedCascadeMarksLaw ρ n : Measure (IndexedCascadeMarks T n))
  let M' := (indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n))
  let a : IndexedCascadeBase n×(IndexedCascadeMarks S n×IndexedCascadeMarks T n) →
      IndexedCascadeBase n×IndexedCascadeMarks (S×T) n :=
    Prod.map id (indexedMarksZip (S:=S) (T:=T) n)
  have ha : Measurable a := measurable_id.prodMap (indexedMarksZip_measurable n)
  have hmap : (B.prod M).map a=B.prod M' := by
    rw [←Measure.map_prod_map _ _ measurable_id (indexedMarksZip_measurable n),Measure.map_id]
    exact congrArg (Measure.prod B) (indexedMarksZip_law ν ρ n)
  have hterm : Measurable (fun p : X×Y => H p.1+G p.2) :=
    (hH.comp measurable_fst).add (hG.comp measurable_snd)
  have hfg : Measurable (fun p : X×Y => f p.1*g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hval := indexedTerminalPairMean_integral (productMarkLaw ν ρ) st hs n z hz hz0 hz1
    (fun p : X×Y => H p.1+G p.2) hterm
    (finiteCascadeFractionalIntegrable_add_product ν ρ step₁ step₂ n z hz0 hHI hGI)
    (x,y) d (fun p : X×Y => f p.1*g p.2) hfg (C*D) (mul_nonneg hC hD)
    (fun p => by rw [abs_mul]; exact mul_le_mul (hfB p.1) (hgB p.2) (abs_nonneg _) hC)
  change (∫ p, indexedTerminalPairMean st n _ _ _ _ p ∂B.prod M')=_ at hval
  rw [←hmap,integral_map ha.aemeasurable
    (indexedTerminalPairMean_measurable st hs n _ hterm (x,y) d _ hfg).aestronglyMeasurable] at hval
  refine hval.trans ?_
  dsimp only [st]
  simp_rw [cascadeTiltedStep_parallel ν ρ step₁ step₂ hs₁ hs₂ n z hz0 H G hH hG hHI hGI]
  rw [pathCorrelation_parallel n _ _
    (cascadeTiltedStep_markov ν step₁ hs₁ n z hz0 H hH hHI)
    (cascadeTiltedStep_markov ρ step₂ hs₂ n z hz0 G hG hGI) f g hf hg C D hC hD hfB hgB]

end SphericalPerceptronFreeEnergy
end

end OAI
