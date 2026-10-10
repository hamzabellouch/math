import Mathlib
import OAI.Probability.Perceptron.Variational.ProductMarkLaw
import OAI.Probability.Perceptron.Variational.TiltedVisitKernel

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X Y S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace S] [MeasurableSpace T]

lemma pathMean_parallel (n : ℕ) (κ : Fin n → Kernel X X) (η : Fin n → Kernel Y Y)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (hη : ∀ i, IsMarkovKernel (η i))
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfB : ∀ x, |f x| ≤ C) (hgB : ∀ y, |g y| ≤ D) (x : X) (y : Y) :
    pathMean n (fun i => κ i ∥ₖ η i) (fun p => f p.1*g p.2) (x,y) =
      pathMean n κ f x * pathMean n η g y := by
  have hfg : Measurable (fun p : X×Y => f p.1*g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hB : ∀ p : X×Y, |f p.1*g p.2| ≤ C*D := fun p => by
    simpa only [abs_mul, abs_of_nonneg hD] using
      mul_le_mul (hfB p.1) ((hgB p.2).trans (le_abs_self D)) (abs_nonneg _) hC
  induction n generalizing x y with
  | zero =>
    simp only [pathMean,pathOneKernel,Kernel.id_apply]
    rw [integral_dirac' _ _ hfg.stronglyMeasurable,
      integral_dirac' _ _ hf.stronglyMeasurable,integral_dirac' _ _ hg.stronglyMeasurable]
  | succ n ih =>
    have := hκ 0
    have := hη 0
    have hpar : ∀ i, IsMarkovKernel (κ i ∥ₖ η i) := by intro i; have := hκ i; have := hη i; infer_instance
    rw [pathMean_succ n _ hpar _ hfg (C*D) hB,
      pathMean_succ n κ hκ f hf C hfB,pathMean_succ n η hη g hg D hgB,
      Kernel.parallelComp_apply]
    simp_rw [ih _ _ (fun i => hκ i.succ) (fun i => hη i.succ)]
    exact integral_prod_mul _ _

lemma pathCorrelation_parallel (n : ℕ) (κ : Fin n → Kernel X X) (η : Fin n → Kernel Y Y)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (hη : ∀ i, IsMarkovKernel (η i))
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfB : ∀ x, |f x| ≤ C) (hgB : ∀ y, |g y| ≤ D) (d : Fin (n+1)) (x : X) (y : Y) :
    pathCorrelation n (fun i => κ i ∥ₖ η i) (fun p => f p.1*g p.2) d (x,y) =
      pathCorrelation n κ f d x * pathCorrelation n η g d y := by
  have hfg : Measurable (fun p : X×Y => f p.1*g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hB : ∀ p : X×Y, |f p.1*g p.2| ≤ C*D := fun p => by
    rw [abs_mul]; exact mul_le_mul (hfB p.1) (hgB p.2) (abs_nonneg _) hC
  induction n generalizing x y with
  | zero =>
    have hd : d=0 := by apply Fin.ext; omega
    rw [hd,pathCorrelation_zero _ _ (fun i => Fin.elim0 i) _ hfg,
      pathCorrelation_zero _ κ hκ f hf,pathCorrelation_zero _ η hη g hg,
      pathMean_parallel 0 κ η hκ hη f g hf hg C D hC hD hfB hgB x y]
    ring
  | succ n ih =>
    have := hκ 0
    have := hη 0
    have hpar : ∀ i, IsMarkovKernel (κ i ∥ₖ η i) := by intro i; have := hκ i; have := hη i; infer_instance
    induction d using Fin.cases with
    | zero =>
      rw [pathCorrelation_zero _ _ hpar _ hfg,pathCorrelation_zero _ κ hκ f hf,
        pathCorrelation_zero _ η hη g hg,
        pathMean_parallel _ κ η hκ hη f g hf hg C D hC hD hfB hgB x y]
      ring
    | succ d =>
      rw [pathCorrelation_succ n _ hpar _ hfg (C*D) (mul_nonneg hC hD) hB,
        pathCorrelation_succ n κ hκ f hf C hC hfB,
        pathCorrelation_succ n η hη g hg D hD hgB,Kernel.parallelComp_apply]
      simp_rw [ih _ _ (fun i => hκ i.succ) (fun i => hη i.succ)]
      exact integral_prod_mul _ _

lemma finiteCascadeShifts_add_product (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (n : ℕ) (z : Fin n→ℝ) (hz : ∀ i, 0<z i)
    {H : X→ℝ} {G : Y→ℝ} (hH : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hG : finiteCascadeFractionalIntegrable ρ step₂ G n z) (i : Fin n) (p : (X×Y)×(S×T)) :
    finiteCascadeShifts (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n z
      (fun x => H x.1+G x.2) i p =
      finiteCascadeShifts ν step₁ n z H i (p.1.1,p.2.1)+
        finiteCascadeShifts ρ step₂ n z G i (p.1.2,p.2.2) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      simp only [finiteCascadeShifts,Fin.cases_zero]
      rw [finiteCascadeLogRecursion_add_product ν ρ step₁ step₂ n _ (fun i => hz i.succ) hH.2 hG.2,
        finiteCascadeLogRecursion_add_product ν ρ step₁ step₂ (n+1) z hz hH hG]
      ring
    | succ i =>
      exact ih (fun i => z i.succ) (fun i => hz i.succ) hH.2 hG.2 i

lemma tiltedStateStep_parallel (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (z : ℝ) (F : X×S→ℝ) (G : Y×T→ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hGI : ∀ y, Integrable (fun t => Real.exp (z*G (y,t))) ρ)
    (hFM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν)=1)
    (hGM : ∀ y, (∫ t, Real.exp (z*G (y,t)) ∂ρ)=1) :
    tiltedStateStep (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) z
      (fun p => F (p.1.1,p.2.1)+G (p.1.2,p.2.2)) =
      tiltedStateStep ν step₁ z F ∥ₖ tiltedStateStep ρ step₂ z G := by
  have hs : Measurable (fun p : (X×Y)×(S×T) =>
      (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) := by fun_prop
  have hFG : Measurable (fun p : (X×Y)×(S×T) => F (p.1.1,p.2.1)+G (p.1.2,p.2.2)) := by fun_prop
  have hI (x : X×Y) : Integrable (fun s : S×T => Real.exp (z*(F (x.1,s.1)+G (x.2,s.2))))
      (productMarkLaw ν ρ) := by
    simp_rw [mul_add,Real.exp_add]
    exact (hFI x.1).mul_prod (hGI x.2)
  have hM (x : X×Y) : (∫ s : S×T, Real.exp (z*(F (x.1,s.1)+G (x.2,s.2)))
      ∂productMarkLaw ν ρ)=1 := by
    simp_rw [mul_add,Real.exp_add]
    change (∫ s : S×T, Real.exp (z*F (x.1,s.1))*Real.exp (z*G (x.2,s.2))
      ∂(ν : Measure S).prod (ρ : Measure T))=1
    exact (integral_prod_mul (fun s => Real.exp (z*F (x.1,s)))
      (fun t => Real.exp (z*G (x.2,t)))).trans (by rw [hFM,hGM,one_mul])
  have := tiltedStateStep_markov ν step₁ hs₁ z F hF hFI hFM
  have := tiltedStateStep_markov ρ step₂ hs₂ z G hG hGI hGM
  apply Kernel.ext
  intro x
  apply Measure.ext_of_lintegral
  intro f hf
  rw [tiltedStateStep_lintegral (productMarkLaw ν ρ) _ hs z _ hFG hI hM f hf,
    Kernel.parallelComp_apply,lintegral_prod _ hf.aemeasurable]
  have hi (a : X) := tiltedStateStep_lintegral ρ step₂ hs₂ z G hG hGI hGM
    (fun b => f (a,b)) (hf.comp (measurable_const.prodMk measurable_id)) x.2
  simp_rw [hi]
  have hm : Measurable (fun a : X => ∫⁻ t, ENNReal.ofReal (Real.exp (z*G (x.2,t)))*
      f (a,step₂ (x.2,t)) ∂ρ) := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun p : X×T => ENNReal.ofReal (Real.exp (z*G (x.2,p.2)))*
      f (p.1,step₂ (x.2,p.2)))
    fun_prop
  rw [tiltedStateStep_lintegral ν step₁ hs₁ z F hF hFI hFM _ hm]
  change (∫⁻ s : S×T, ENNReal.ofReal (Real.exp (z*(F (x.1,s.1)+G (x.2,s.2))))*
    f (step₁ (x.1,s.1),step₂ (x.2,s.2)) ∂(ν : Measure S).prod (ρ : Measure T))=_
  rw [lintegral_prod]
  · apply lintegral_congr
    intro s
    rw [←lintegral_const_mul]
    · apply lintegral_congr
      intro t
      rw [mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact mul_assoc _ _ _
    · fun_prop
  · fun_prop

end SphericalPerceptronFreeEnergy
end

end OAI
