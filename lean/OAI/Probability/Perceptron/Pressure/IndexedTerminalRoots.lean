import Mathlib
import OAI.Probability.Perceptron.Pressure.IndexedTerminalProduct

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
section
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

lemma indexedTerminalPairMean_joint_measurable (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (d : Fin (n+1))
    (f : X→ℝ) (hf : Measurable f) :
    Measurable (fun p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n) =>
      indexedTerminalPairMean step n H p.1 d f p.2) := by
  let β : Kernel (X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (IndexedLeaf n) :=
    (indexedTerminalBaseKernel n).comap Prod.snd measurable_snd
  let E : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))→IndexedLeaf n→ℝ :=
    fun p l => H (indexedLeafState step n (p.1,p.2.2) l)
  have hE : Measurable (Function.uncurry E) :=
    hH.comp ((indexedLeafState_measurable hs n).comp
      ((measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd))
  let κ := gibbsProbabilityKernel β E
  have : IsMarkovKernel β := by dsimp [β]; infer_instance
  have : IsMarkovKernel κ := gibbsProbabilityKernel_markov β E hE
  have he (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) :
      κ p=gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H p.1) p.2 :=
    gibbsProbabilityKernel_congr_apply β E (indexedTerminalBaseKernel n)
      (indexedTerminalEnergy step n H p.1) hE
      (indexedTerminalEnergy_measurable step hs n H hH p.1) p p.2
      (by simp [β]) rfl
  let F : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))×(IndexedLeaf n×IndexedLeaf n)→ℝ :=
    fun p => if indexedCommonDepth n p.2.1 p.2.2=d then
      f (indexedLeafState step n (p.1.1,p.1.2.2) p.2.1)*
      f (indexedLeafState step n (p.1.1,p.1.2.2) p.2.2) else 0
  have hm (j : IndexedLeaf n×IndexedLeaf n→IndexedLeaf n) (hj : Measurable j) :
      Measurable (fun p : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))×(IndexedLeaf n×IndexedLeaf n) =>
        f (indexedLeafState step n (p.1.1,p.1.2.2) (j p.2))) :=
    hf.comp ((indexedLeafState_measurable hs n).comp
      ((measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk (hj.comp measurable_snd)))
  have hcond : MeasurableSet {p : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))×(IndexedLeaf n×IndexedLeaf n) |
      indexedCommonDepth n p.2.1 p.2.2=d} :=
    ((Set.to_countable {l : IndexedLeaf n×IndexedLeaf n | indexedCommonDepth n l.1 l.2=d}).measurableSet).preimage measurable_snd
  have hF : Measurable F :=
    Measurable.ite hcond ((hm Prod.fst measurable_fst).mul (hm Prod.snd measurable_snd)) measurable_const
  have hv : Measurable (fun p => ∫ l, F (p,l) ∂(κ×ₖκ) p) :=
    (hF.stronglyMeasurable.integral_kernel_prod_right').measurable
  simp_rw [Kernel.prod_apply,he] at hv
  unfold indexedTerminalPairMean
  simpa only [F] using hv

end
variable {X Y S T R Q : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace S] [MeasurableSpace T] [Nonempty S] [Nonempty T]
  [MeasurableSpace R] [MeasurableSpace Q]

lemma indexedTerminalPairMean_independent_roots
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z)
    (x : R→X) (y : Q→Y) (hx : Measurable x) (hy : Measurable y) (d : Fin (n+1))
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ x, |f x|≤C) (hgB : ∀ y, |g y|≤D) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    (∫ p, indexedTerminalPairMean st n (fun p => H p.1+G p.2) (x p.1.1,y p.1.2) d
      (fun p => f p.1*g p.2) (p.2.1,indexedMarksZip n p.2.2)
      ∂((μ : Measure R).prod (σ : Measure Q)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
            (indexedCascadeMarksLaw ρ n)))) =
      (twoVisitMass n z d).toReal *
        ((∫ r, pathCorrelation n (fun i => tiltedStateStep ν step₁ (z i) (finiteCascadeShifts ν step₁ n z H i)) f d (x r) ∂μ) *
          (∫ q, pathCorrelation n (fun i => tiltedStateStep ρ step₂ (z i) (finiteCascadeShifts ρ step₂ n z G i)) g d (y q) ∂σ)) := by
  dsimp only
  let st : (X×Y)×(S×T)→X×Y := fun p => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
  let term : X×Y→ℝ := fun p => H p.1+G p.2
  let obs : X×Y→ℝ := fun p => f p.1*g p.2
  have hs : Measurable st := by fun_prop
  have hterm : Measurable term := by fun_prop
  have hfg : Measurable obs := by fun_prop
  have hb (p : X×Y) : |f p.1*g p.2|≤C*D := by
    rw [abs_mul]; exact mul_le_mul (hfB p.1) (hgB p.2) (abs_nonneg _) hC
  let V : (R×Q)×(IndexedCascadeBase n×(IndexedCascadeMarks S n×IndexedCascadeMarks T n))→ℝ :=
    fun p => indexedTerminalPairMean st n term (x p.1.1,y p.1.2) d obs (p.2.1,indexedMarksZip n p.2.2)
  let B := IndexedCascadeBase n×(IndexedCascadeMarks S n×IndexedCascadeMarks T n)
  let transport : (R×Q)×B→(X×Y)×(IndexedCascadeBase n×IndexedCascadeMarks (S×T) n) :=
    fun p => ((x p.1.1,y p.1.2),(p.2.1,indexedMarksZip n p.2.2))
  have hzip : Measurable (indexedMarksZip (S:=S) (T:=T) n) := indexedMarksZip_measurable n
  have htransport : Measurable transport :=
    (((hx.comp (measurable_fst.fst : Measurable (fun p : (R×Q)×B => p.1.1))).prodMk
      (hy.comp measurable_fst.snd)).prodMk
      (measurable_snd.fst.prodMk (hzip.comp measurable_snd.snd)))
  have hjoint := indexedTerminalPairMean_joint_measurable st hs n term hterm d obs hfg
  have hV' := hjoint.comp htransport
  have hV : Measurable V := hV'
  have hi : Integrable V (((μ : Measure R).prod (σ : Measure Q)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
            (indexedCascadeMarksLaw ρ n)))) :=
    Integrable.of_bound hV.aestronglyMeasurable ((C*D)^2) (ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs] using indexedTerminalPairMean_bound st hs n term hterm
        (x p.1.1,y p.1.2) d obs (C*D) (mul_nonneg hC hD) hb _)
  change (∫ p, V p ∂_)=_
  rw [integral_prod _ hi]
  simp_rw [V,term,obs,st,indexedTerminalPairMean_independent_arrays ν ρ step₁ step₂ hs₁ hs₂ n z hz hz0 hz1
    H G hH hG hHI hGI _ _ d f g hf hg C D hC hD hfB hgB]
  rw [integral_const_mul]
  exact congrArg ((twoVisitMass n z d).toReal * ·)
    (integral_prod_mul
      (fun r => pathCorrelation n (fun i => tiltedStateStep ν step₁ (z i)
        (finiteCascadeShifts ν step₁ n z H i)) f d (x r))
      (fun q => pathCorrelation n (fun i => tiltedStateStep ρ step₂ (z i)
        (finiteCascadeShifts ρ step₂ n z G i)) g d (y q)))

end SphericalPerceptronFreeEnergy
end

end OAI
