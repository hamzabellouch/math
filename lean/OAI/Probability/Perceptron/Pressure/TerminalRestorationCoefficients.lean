import Mathlib
import OAI.Probability.Perceptron.Pressure.IndexedTerminalRoots
import OAI.Probability.Perceptron.Variational.TiltedPathDiagonal

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

section
section
variable {X Y R Q S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace R] [MeasurableSpace Q] [MeasurableSpace S] [MeasurableSpace T]
  [Nonempty S] [Nonempty T]

lemma indexedTerminalPairMean_ignore_old
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z)
    (x : R→X) (y : Q→Y) (hx : Measurable x) (hy : Measurable y) (d : Fin (n+1))
    (f : X→ℝ) (hf : Measurable f) (C : ℝ) (hC : 0≤C) (hfB : ∀ x, |f x|≤C) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    (∫ p, indexedTerminalPairMean st n (fun p => H p.1+G p.2) (x p.1.1,y p.1.2) d
      (fun p => f p.1) (p.2.1,indexedMarksZip n p.2.2)
      ∂((μ : Measure R).prod (σ : Measure Q)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
            (indexedCascadeMarksLaw ρ n)))) =
      (twoVisitMass n z d).toReal * rootPathCorrelation μ x n
        (fun i => tiltedStateStep ν step₁ (z i) (finiteCascadeShifts ν step₁ n z H i)) f d := by
  have h := indexedTerminalPairMean_independent_roots μ σ ν ρ step₁ step₂ hs₁ hs₂
    n z hz hz0 hz1 H G hH hG hHI hGI x y hx hy d f (fun _ => 1)
    hf measurable_const C 1 hC (by norm_num) hfB (fun _ => by norm_num)
  have hm i := cascadeTiltedStep_markov ρ step₂ hs₂ n z hz0 G hG hGI i
  simpa only [mul_one,pathCorrelation_one n _ hm,integral_const,probReal_univ,
    one_smul,rootPathCorrelation] using h

omit [Nonempty S] [Nonempty T] in
lemma cascade_root_pair_coefficients_product
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz0 : ∀ i, 0<z i)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z)
    (x : R→X) (y : Q→Y) (d : Fin (n+1))
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ x, |f x|≤C) (hgB : ∀ y, |g y|≤D) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    rootPathCorrelation ((μ : Measure R).prod (σ : Measure Q)) (fun r => (x r.1,y r.2)) n
      (fun i => tiltedStateStep (productMarkLaw ν ρ) st (z i)
        (finiteCascadeShifts (productMarkLaw ν ρ) st n z (fun p => H p.1+G p.2) i))
      (fun p => f p.1*g p.2) d =
      rootPathCorrelation μ x n (fun i => tiltedStateStep ν step₁ (z i)
        (finiteCascadeShifts ν step₁ n z H i)) f d *
      rootPathCorrelation σ y n (fun i => tiltedStateStep ρ step₂ (z i)
        (finiteCascadeShifts ρ step₂ n z G i)) g d := by
  dsimp only
  simp_rw [cascadeTiltedStep_parallel ν ρ step₁ step₂ hs₁ hs₂ n z hz0 H G hH hG hHI hGI]
  exact rootPathCorrelation_parallel μ σ x y n _ _
    (fun i => cascadeTiltedStep_markov ν step₁ hs₁ n z hz0 H hH hHI i)
    (fun i => cascadeTiltedStep_markov ρ step₂ hs₂ n z hz0 G hG hGI i)
    f g hf hg C D hC hD hfB hgB d

end
variable {X R : Type} [MeasurableSpace X] [MeasurableSpace R]

lemma residual_path_pair_coefficients
    (μ : Measure R) [IsProbabilityMeasure μ] (x : R→X) (hx : Measurable x)
    (n : ℕ) (κ : Fin n→Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (e : X→ℝ) (he : Measurable e) (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) :
    (∀ d, 0≤rootPathCorrelation μ x n κ (fun y => residualResponse s f v (e y)) d) ∧
    Monotone (rootPathCorrelation μ x n κ (fun y => residualResponse s f v (e y))) ∧
    (∀ d, rootPathCorrelation μ x n κ (fun y => residualResponse s f v (e y)) d ≤
      rootPathMean μ x n κ (fun y => residualResponse s f (v*v) (e y))) ∧
    (rootPathMean μ x n κ (fun y => residualResponse s f (v*v) (e y))≤‖v‖^2) := by
  have hv := (residualResponse_continuous s f v).measurable.comp he
  have hvv := (residualResponse_continuous s f (v*v)).measurable.comp he
  have hb := fun y => residualResponse_bound s f v (e y)
  have hbb := fun y => residualResponse_bound s f (v*v) (e y)
  refine ⟨fun d => rootPathCorrelation_nonneg μ x n κ hκ _ hv _ (norm_nonneg _) hb d,
    rootPathCorrelation_monotone μ x hx n κ hκ _ hv _ (norm_nonneg _) hb,?_,?_⟩
  · intro d
    exact rootPathCorrelation_le_diagonal μ x hx n κ hκ _ _ hv hvv _ _
      (norm_nonneg _) hb hbb (fun y => residualResponse_jensen s f v (e y)) d
  · apply (le_abs_self _).trans
    apply (show |rootPathMean μ x n κ (fun y => residualResponse s f (v*v) (e y))|≤‖v*v‖ from ?_).trans
    · simpa only [pow_two] using norm_mul_le v v
    · simpa only [rootPathMean,Real.norm_eq_abs,probReal_univ,mul_one] using
        norm_integral_le_of_norm_le_const
          (μ:=μ) (f:=fun r => pathMean n κ (fun y => residualResponse s f (v*v) (e y)) (x r))
          (ae_of_all _ fun r => by
            simpa only [Real.norm_eq_abs] using pathMean_bound n κ hκ _ ‖v*v‖ hbb (x r))

end
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

def indexedTerminalMean (step : X×S→X) (n : ℕ) (H : X→ℝ) (x : X)
    (f : X→ℝ) (p : IndexedCascadeBase n×IndexedCascadeMarks S n) : ℝ :=
  ∫ l, f (indexedLeafState step n (x,p.2) l)
    ∂gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H x) p

lemma indexedTerminalMean_joint_measurable (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (f : X→ℝ) (hf : Measurable f) :
    Measurable (fun p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n) =>
      indexedTerminalMean step n H p.1 f p.2) := by
  let β : Kernel (X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (IndexedLeaf n) :=
    (indexedTerminalBaseKernel n).comap Prod.snd measurable_snd
  let E : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))→IndexedLeaf n→ℝ :=
    fun p l => H (indexedLeafState step n (p.1,p.2.2) l)
  have hstate : Measurable (fun p : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))×IndexedLeaf n =>
      indexedLeafState step n (p.1.1,p.1.2.2) p.2) := (indexedLeafState_measurable hs n).comp
    ((measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd)
  have hE : Measurable (Function.uncurry E) := hH.comp hstate
  let κ := gibbsProbabilityKernel β E
  have : IsMarkovKernel β := by dsimp [β]; infer_instance
  have : IsMarkovKernel κ := gibbsProbabilityKernel_markov β E hE
  have he (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) :
      κ p=gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H p.1) p.2 :=
    gibbsProbabilityKernel_congr_apply β E (indexedTerminalBaseKernel n)
      (indexedTerminalEnergy step n H p.1) hE
      (indexedTerminalEnergy_measurable step hs n H hH p.1) p p.2
      (by simp [β]) rfl
  have hm := (hf.comp hstate).stronglyMeasurable.integral_kernel_prod_right' (κ:=κ)
  simpa only [he,indexedTerminalMean,Function.comp_apply] using hm.measurable

lemma indexedTerminalMean_bound (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (x : X) (f : X→ℝ)
    (C : ℝ) (hb : ∀ y, |f y|≤C) (p : IndexedCascadeBase n×IndexedCascadeMarks S n) :
    |indexedTerminalMean step n H x f p|≤C := by
  have := gibbsProbabilityKernel_markov (indexedTerminalBaseKernel n) _
    (indexedTerminalEnergy_measurable step hs n H hH x)
  simpa only [indexedTerminalMean,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H x) p)
      (f:=fun l => f (indexedLeafState step n (x,p.2) l))
      (ae_of_all _ fun l => by simpa only [Real.norm_eq_abs] using hb (indexedLeafState step n (x,p.2) l))

variable [Nonempty S]
lemma indexedTerminalMean_integral (ν : ProbabilityMeasure S) (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z)
    (x : X) (f : X→ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ y, |f y|≤C) :
    (∫ p, indexedTerminalMean step n H x f p
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      pathMean n (fun i => tiltedStateStep ν step (z i) (finiteCascadeShifts ν step n z H i)) f x := by
  let μ := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))
  let F := finiteCascadeShifts ν step n z H
  have hF := finiteCascadeShifts_measurable ν step hs n z hH
  let κ := indexedOneStateKernel step hs n F hF x
  have he : (fun p => indexedTerminalMean step n H x f p)=ᵐ[μ]
      (fun p => ∫ y, f y ∂κ p) := by
    have hi := indexed_terminal_exp_integrable_ae ν step hs n z hz hz0 hz1 H hH hI x
    have hb₀ := (measurePreserving_fst (μ := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)))
      (ν := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))).quasiMeasurePreserving.ae
        (indexedLeafMeasure_regular n z hz hz0 hz1)
    filter_upwards [hi,hb₀] with p hi hp
    unfold indexedTerminalMean
    rw [gibbsProbabilityKernel_of_integrable (indexedTerminalBaseKernel n) _
      (indexedTerminalEnergy_measurable step hs n H hH x) p hi]
    have hmap := indexed_terminal_oneState ν step hs n z H hH x p.1 p.2 hp hi
    have hh := integral_map (μ:=tiltLaw (indexedLeafProbability n p.1)
      (fun l => H (indexedLeafState step n (x,p.2) l)) 1)
      (measurable_of_countable (indexedLeafState step n (x,p.2))).aemeasurable hf.aestronglyMeasurable
    rw [hmap] at hh
    exact hh.symm
  rw [integral_congr_ae he]
  have hnorm := finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz0 i).ne') H hI
  have hi := path_bounded_integrable (κ ∘ₘ μ) f hf C hb
  have hcomp : (∫ y, f y ∂(κ ∘ₘ μ))=∫ p, ∫ y, f y ∂κ p ∂μ := by
    rw [Measure.comp_eq_comp_const_apply] at hi ⊢
    exact Kernel.integral_comp hi
  rw [←hcomp]
  change (∫ y, f y ∂(indexedOneStateKernel step hs n F hF x ∘ₘ μ))=_
  rw [indexedOneStateLaw_eq ν step hs n z hz hz0 hz1 F hF
    (fun i y => (hnorm i y).1) (fun i y => (hnorm i y).2)]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
