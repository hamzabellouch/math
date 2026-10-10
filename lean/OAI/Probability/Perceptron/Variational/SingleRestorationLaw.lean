import Mathlib
import OAI.Probability.Perceptron.Pressure.TerminalRestorationLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
section
variable {X R : Type} [MeasurableSpace X] [MeasurableSpace R]
lemma rootPathMean_one (μ : Measure R) [IsProbabilityMeasure μ] (x : R→X)
    (n : ℕ) (κ : Fin n→Kernel X X) (hκ : ∀ i,IsMarkovKernel (κ i)) :
    rootPathMean μ x n κ (fun _ => 1)=1 := by
  have := pathOneKernel_markov n κ hκ
  simp [rootPathMean,pathMean]
end
section
variable {X Y R Q S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace R] [MeasurableSpace Q] [MeasurableSpace S] [MeasurableSpace T]
  [Nonempty S] [Nonempty T]
lemma indexedTerminalMean_independent_roots
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z)
    (x : R→X) (y : Q→Y) (hx : Measurable x) (hy : Measurable y)
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ a,|f a|≤C) (hgB : ∀ b,|g b|≤D) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    (∫ p,indexedTerminalMean st n (fun p => H p.1+G p.2) (x p.1.1,y p.1.2)
      (fun p => f p.1*g p.2) (p.2.1,indexedMarksZip n p.2.2)
      ∂((μ : Measure R).prod (σ : Measure Q)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
            (indexedCascadeMarksLaw ρ n)))) =
      rootPathMean μ x n (fun i => tiltedStateStep ν step₁ (z i)
        (finiteCascadeShifts ν step₁ n z H i)) f *
      rootPathMean σ y n (fun i => tiltedStateStep ρ step₂ (z i)
        (finiteCascadeShifts ρ step₂ n z G i)) g := by
  dsimp only
  let st : (X×Y)×(S×T)→X×Y := fun p => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
  have hs : Measurable st := by fun_prop
  have hterm : Measurable (fun p : X×Y => H p.1+G p.2) := by fun_prop
  have hobs : Measurable (fun p : X×Y => f p.1*g p.2) := by fun_prop
  have hb (p : X×Y) : |f p.1*g p.2|≤C*D := by
    rw [abs_mul]; exact mul_le_mul (hfB _) (hgB _) (abs_nonneg _) hC
  have hzmap : MeasurePreserving (indexedMarksZip (S:=S) (T:=T) n)
      ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
        (indexedCascadeMarksLaw ρ n)) (indexedCascadeMarksLaw (productMarkLaw ν ρ) n) :=
    ⟨indexedMarksZip_measurable n,indexedMarksZip_law ν ρ n⟩
  have hp := (MeasurePreserving.id ((μ : Measure R).prod (σ : Measure Q))).prod
    ((MeasurePreserving.id (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n))).prod hzmap)
  let F : (R×Q)×(IndexedCascadeBase n×IndexedCascadeMarks (S×T) n)→ℝ :=
    fun p => indexedTerminalMean st n (fun p => H p.1+G p.2) (x p.1.1,y p.1.2)
      (fun p => f p.1*g p.2) p.2
  let D₀ := (R×Q)×(IndexedCascadeBase n×IndexedCascadeMarks (S×T) n)
  let tr : D₀→(X×Y)×(IndexedCascadeBase n×IndexedCascadeMarks (S×T) n) :=
    fun p => ((x p.1.1,y p.1.2),p.2)
  have htr : Measurable tr :=
    (((hx.comp (measurable_fst.fst : Measurable (fun p : D₀ => p.1.1))).prodMk
      (hy.comp measurable_fst.snd)).prodMk measurable_snd)
  have hj := indexedTerminalMean_joint_measurable st hs n
    (fun p => H p.1+G p.2) hterm (fun p => f p.1*g p.2) hobs
  have hm' := hj.comp htr
  have hm : Measurable F := hm'
  have he := integral_map (μ:=((μ : Measure R).prod (σ : Measure Q)).prod
      ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
          (indexedCascadeMarksLaw ρ n)))) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  dsimp only [F,Prod.map_apply,id_eq] at he
  have hv := indexedTerminalMean_root_integral
    (productMarkLaw μ σ) (productMarkLaw ν ρ) st hs n z hz hz0 hz1 _ hterm
    (finiteCascadeFractionalIntegrable_add_product ν ρ step₁ step₂ n z hz0 hHI hGI)
    (fun p => (x p.1,y p.2)) (by fun_prop) _ hobs (C*D) hb
  have hc := cascade_root_single_coefficients_product μ σ ν ρ step₁ step₂ hs₁ hs₂ n z hz0
    H G hH hG hHI hGI x y f g hf hg C D hC hD hfB hgB
  exact he.symm.trans (hv.trans hc)

lemma indexedTerminalMean_ignore_old
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z)
    (x : R→X) (y : Q→Y) (hx : Measurable x) (hy : Measurable y)
    (f : X→ℝ) (hf : Measurable f) (C : ℝ) (hC : 0≤C) (hfB : ∀ a,|f a|≤C) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    (∫ p,indexedTerminalMean st n (fun p => H p.1+G p.2) (x p.1.1,y p.1.2)
      (fun p => f p.1) (p.2.1,indexedMarksZip n p.2.2)
      ∂((μ : Measure R).prod (σ : Measure Q)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
            (indexedCascadeMarksLaw ρ n)))) =
      rootPathMean μ x n (fun i => tiltedStateStep ν step₁ (z i)
        (finiteCascadeShifts ν step₁ n z H i)) f := by
  have h := indexedTerminalMean_independent_roots μ σ ν ρ step₁ step₂ hs₁ hs₂
    n z hz hz0 hz1 H G hH hG hHI hGI x y hx hy f (fun _ => 1)
    hf measurable_const C 1 hC (by norm_num) hfB (fun _ => by norm_num)
  have hm i := cascadeTiltedStep_markov ρ step₂ hs₂ n z hz0 G hG hGI i
  simpa only [rootPathMean_one σ y n _ hm,mul_one] using h
end
variable {X Y Z R Q U S T V : Type}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace R] [MeasurableSpace Q] [MeasurableSpace U]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace V]
  [Nonempty S] [Nonempty T] [Nonempty V]

lemma indexedTerminalMean_two_fresh_old
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
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ a, |f a|≤C) (hgB : ∀ b, |g b|≤D) :
    let st := fun p : ((X×Y)×Z)×((S×T)×V) =>
      ((st₁ (p.1.1.1,p.2.1.1),st₂ (p.1.1.2,p.2.1.2)),st₀ (p.1.2,p.2.2))
    (∫ p, indexedTerminalMean st n (fun p => (H p.1.1+G p.1.2)+J p.2)
      ((x p.1.1.1,y p.1.1.2),v p.1.2) (fun p => f p.1.1*g p.1.2)
      (p.2.1,indexedMarksZip n p.2.2)
      ∂(((μ : Measure R).prod (σ : Measure Q)).prod (τ : Measure U)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n)).prod
            (indexedCascadeMarksLaw π n)))) =
      (rootPathMean μ x n (fun i => tiltedStateStep ν st₁ (z i)
          (finiteCascadeShifts ν st₁ n z H i)) f *
        rootPathMean σ y n (fun i => tiltedStateStep ρ st₂ (z i)
          (finiteCascadeShifts ρ st₂ n z G i)) g) := by
  let st : (X×Y)×(S×T)→X×Y := fun p => (st₁ (p.1.1,p.2.1),st₂ (p.1.2,p.2.2))
  have hs : Measurable st := by fun_prop
  have hfg : Measurable (fun p : X×Y => f p.1*g p.2) := by fun_prop
  have hb (p : X×Y) : |f p.1*g p.2|≤C*D := by
    rw [abs_mul]; exact mul_le_mul (hfB _) (hgB _) (abs_nonneg _) hC
  have h := indexedTerminalMean_ignore_old (productMarkLaw μ σ) τ (productMarkLaw ν ρ) π
    st st₀ hs hs₀ n z hz hz0 hz1 (fun p => H p.1+G p.2) J (by fun_prop) hJ
    (finiteCascadeFractionalIntegrable_add_product ν ρ st₁ st₂ n z hz0 hHI hGI) hJI
    (fun p => (x p.1,y p.2)) v (by fun_prop) hv (fun p => f p.1*g p.2) hfg
    (C*D) (mul_nonneg hC hD) hb
  dsimp only [st] at h ⊢
  change _ = rootPathMean ((μ : Measure R).prod (σ : Measure Q)) (fun p => (x p.1,y p.2)) n
      (fun i => tiltedStateStep (productMarkLaw ν ρ)
        (fun p => (st₁ (p.1.1,p.2.1),st₂ (p.1.2,p.2.2))) (z i)
        (finiteCascadeShifts (productMarkLaw ν ρ)
          (fun p => (st₁ (p.1.1,p.2.1),st₂ (p.1.2,p.2.2))) n z (fun p => H p.1+G p.2) i))
      (fun p => f p.1*g p.2) at h
  rw [cascade_root_single_coefficients_product μ σ ν ρ st₁ st₂ hs₁ hs₂ n z hz0
    H G hH hG hHI hGI x y f g hf hg C D hC hD hfB hgB] at h
  exact h

end SphericalPerceptronFreeEnergy
end

end OAI
