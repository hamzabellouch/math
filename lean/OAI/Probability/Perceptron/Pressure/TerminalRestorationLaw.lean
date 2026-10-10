import Mathlib
import OAI.Probability.Perceptron.Pressure.TerminalRestorationCoefficients

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
section
variable {X R S : Type} [MeasurableSpace X] [MeasurableSpace R] [MeasurableSpace S] [Nonempty S]

lemma indexedTerminalMean_root_integral (μ : ProbabilityMeasure R) (ν : ProbabilityMeasure S)
    (step : X×S→X) (hs : Measurable step) (n : ℕ) (z : Fin n→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z)
    (x : R→X) (hx : Measurable x) (f : X→ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ y, |f y|≤C) :
    (∫ p, indexedTerminalMean step n H (x p.1) f p.2
      ∂(μ : Measure R).prod ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))) =
      rootPathMean μ x n (fun i => tiltedStateStep ν step (z i) (finiteCascadeShifts ν step n z H i)) f := by
  let V : R×(IndexedCascadeBase n×IndexedCascadeMarks S n)→ℝ :=
    fun p => indexedTerminalMean step n H (x p.1) f p.2
  have hm := (indexedTerminalMean_joint_measurable step hs n H hH f hf).comp
    ((hx.comp measurable_fst).prodMk measurable_snd)
  have hV : Measurable V := hm
  have hi : Integrable V ((μ : Measure R).prod ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))) := by
    apply Integrable.of_bound hV.aestronglyMeasurable C
    exact ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs] using indexedTerminalMean_bound step hs n H hH (x p.1) f C hb p.2
  change (∫ p, V p ∂_)=_
  rw [integral_prod _ hi]
  simp only [V,indexedTerminalMean_integral ν step hs n z hz hz0 hz1 H hH hI _ f hf C hb,rootPathMean]

end
section
variable {X Y R Q S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace R] [MeasurableSpace Q] [MeasurableSpace S] [MeasurableSpace T]

lemma rootPathMean_parallel (μ : Measure R) (σ : Measure Q) [SFinite μ] [SFinite σ]
    (x : R→X) (y : Q→Y) (n : ℕ) (κ : Fin n→Kernel X X) (η : Fin n→Kernel Y Y)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (hη : ∀ i, IsMarkovKernel (η i))
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ a, |f a|≤C) (hgB : ∀ b, |g b|≤D) :
    rootPathMean (μ.prod σ) (fun p => (x p.1,y p.2)) n (fun i => κ i ∥ₖ η i)
      (fun p => f p.1*g p.2) = rootPathMean μ x n κ f * rootPathMean σ y n η g := by
  unfold rootPathMean
  simp_rw [pathMean_parallel n κ η hκ hη f g hf hg C D hC hD hfB hgB]
  exact integral_prod_mul (fun r => pathMean n κ f (x r)) (fun q => pathMean n η g (y q))

lemma cascade_root_single_coefficients_product
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz0 : ∀ i, 0<z i)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z)
    (x : R→X) (y : Q→Y) (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ x, |f x|≤C) (hgB : ∀ y, |g y|≤D) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    rootPathMean ((μ : Measure R).prod (σ : Measure Q)) (fun r => (x r.1,y r.2)) n
      (fun i => tiltedStateStep (productMarkLaw ν ρ) st (z i)
        (finiteCascadeShifts (productMarkLaw ν ρ) st n z (fun p => H p.1+G p.2) i))
      (fun p => f p.1*g p.2) =
      rootPathMean μ x n (fun i => tiltedStateStep ν step₁ (z i)
        (finiteCascadeShifts ν step₁ n z H i)) f *
      rootPathMean σ y n (fun i => tiltedStateStep ρ step₂ (z i)
        (finiteCascadeShifts ρ step₂ n z G i)) g := by
  dsimp only
  simp_rw [cascadeTiltedStep_parallel ν ρ step₁ step₂ hs₁ hs₂ n z hz0 H G hH hG hHI hGI]
  exact rootPathMean_parallel μ σ x y n _ _
    (fun i => cascadeTiltedStep_markov ν step₁ hs₁ n z hz0 H hH hHI i)
    (fun i => cascadeTiltedStep_markov ρ step₂ hs₂ n z hz0 G hG hGI i)
    f g hf hg C D hC hD hfB hgB

end
variable {X Y Z R Q U S T V : Type}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace R] [MeasurableSpace Q] [MeasurableSpace U]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace V]
  [Nonempty S] [Nonempty T] [Nonempty V]

lemma indexedTerminalPairMean_two_fresh_old
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (τ : ProbabilityMeasure U)
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T) (π : ProbabilityMeasure V)
    (st₁ : X×S→X) (st₂ : Y×T→Y) (st₀ : Z×V→Z)
    (hs₁ : Measurable st₁) (hs₂ : Measurable st₂) (hs₀ : Measurable st₀)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (G : Y→ℝ) (J : Z→ℝ) (hH : Measurable H) (hG : Measurable G) (hJ : Measurable J)
    (hHI : finiteCascadeFractionalIntegrable ν st₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ st₂ G n z)
    (hJI : finiteCascadeFractionalIntegrable π st₀ J n z)
    (x : R→X) (y : Q→Y) (v : U→Z) (hx : Measurable x) (hy : Measurable y) (hv : Measurable v)
    (d : Fin (n+1)) (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ a, |f a|≤C) (hgB : ∀ b, |g b|≤D) :
    let st := fun p : ((X×Y)×Z)×((S×T)×V) =>
      ((st₁ (p.1.1.1,p.2.1.1),st₂ (p.1.1.2,p.2.1.2)),st₀ (p.1.2,p.2.2))
    (∫ p, indexedTerminalPairMean st n (fun p => (H p.1.1+G p.1.2)+J p.2)
      ((x p.1.1.1,y p.1.1.2),v p.1.2) d (fun p => f p.1.1*g p.1.2)
      (p.2.1,indexedMarksZip n p.2.2)
      ∂(((μ : Measure R).prod (σ : Measure Q)).prod (τ : Measure U)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n)).prod
            (indexedCascadeMarksLaw π n)))) =
      (twoVisitMass n z d).toReal *
        (rootPathCorrelation μ x n (fun i => tiltedStateStep ν st₁ (z i)
          (finiteCascadeShifts ν st₁ n z H i)) f d *
        rootPathCorrelation σ y n (fun i => tiltedStateStep ρ st₂ (z i)
          (finiteCascadeShifts ρ st₂ n z G i)) g d) := by
  let st : (X×Y)×(S×T)→X×Y := fun p => (st₁ (p.1.1,p.2.1),st₂ (p.1.2,p.2.2))
  have hs : Measurable st := by fun_prop
  have hfg : Measurable (fun p : X×Y => f p.1*g p.2) := by fun_prop
  have hb (p : X×Y) : |f p.1*g p.2|≤C*D := by
    rw [abs_mul]; exact mul_le_mul (hfB _) (hgB _) (abs_nonneg _) hC
  have h := indexedTerminalPairMean_ignore_old (productMarkLaw μ σ) τ (productMarkLaw ν ρ) π
    st st₀ hs hs₀ n z hz hz0 hz1 (fun p => H p.1+G p.2) J (by fun_prop) hJ
    (finiteCascadeFractionalIntegrable_add_product ν ρ st₁ st₂ n z hz0 hHI hGI) hJI
    (fun p => (x p.1,y p.2)) v (by fun_prop) hv d (fun p => f p.1*g p.2) hfg
    (C*D) (mul_nonneg hC hD) hb
  dsimp only [st] at h ⊢
  change _ = (twoVisitMass n z d).toReal *
    rootPathCorrelation ((μ : Measure R).prod (σ : Measure Q)) (fun p => (x p.1,y p.2)) n
      (fun i => tiltedStateStep (productMarkLaw ν ρ)
        (fun p => (st₁ (p.1.1,p.2.1),st₂ (p.1.2,p.2.2))) (z i)
        (finiteCascadeShifts (productMarkLaw ν ρ)
          (fun p => (st₁ (p.1.1,p.2.1),st₂ (p.1.2,p.2.2))) n z (fun p => H p.1+G p.2) i))
      (fun p => f p.1*g p.2) d at h
  rw [cascade_root_pair_coefficients_product μ σ ν ρ st₁ st₂ hs₁ hs₂ n z hz0
    H G hH hG hHI hGI x y d f g hf hg C D hC hD hfB hgB] at h
  exact h

end SphericalPerceptronFreeEnergy
end

end OAI
