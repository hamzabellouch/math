import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

def tiltedMarkKernel (ν : ProbabilityMeasure S) (z : ℝ) (F : X×S → ℝ) : Kernel X S :=
  (Kernel.const X (ν : Measure S)).withDensity
    (fun x s => ENNReal.ofReal (Real.exp (z*F (x,s))))

lemma tiltedMarkKernel_markov (ν : ProbabilityMeasure S) (z : ℝ) (F : X×S → ℝ)
    (hF : Measurable F) (hI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν) = 1) :
    IsMarkovKernel (tiltedMarkKernel ν z F) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [tiltedMarkKernel,Kernel.withDensity_apply _ ((hF.const_mul z).exp.ennreal_ofReal)]
  simp only [Kernel.const_apply,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hI x)
    (Filter.Eventually.of_forall (fun s => (Real.exp_pos _).le)),hM x]
  exact ENNReal.ofReal_one

def tiltedStateStep (ν : ProbabilityMeasure S) (step : X×S → X)
    (z : ℝ) (F : X×S → ℝ) : Kernel X X :=
  (Kernel.id ×ₖ tiltedMarkKernel ν z F).map step

lemma tiltedStateStep_markov (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (z : ℝ) (F : X×S → ℝ)
    (hF : Measurable F) (hI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν) = 1) :
    IsMarkovKernel (tiltedStateStep ν step z F) := by
  have := tiltedMarkKernel_markov ν z F hF hI hM
  exact Kernel.IsMarkovKernel.map _ hs

lemma tiltedStateStep_lintegral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (z : ℝ) (F : X×S → ℝ)
    (hF : Measurable F) (hI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν) = 1)
    (h : X → ℝ≥0∞) (hh : Measurable h) (x : X) :
    (∫⁻ y, h y ∂tiltedStateStep ν step z F x) =
      ∫⁻ s, ENNReal.ofReal (Real.exp (z*F (x,s)))*h (step (x,s)) ∂ν := by
  have := tiltedMarkKernel_markov ν z F hF hI hM
  rw [tiltedStateStep,Kernel.lintegral_map _ hs _ hh,
    Kernel.lintegral_id_prod (show Measurable (fun p : X×S => h (step p)) from hh.comp hs)]
  exact Kernel.lintegral_withDensity _ ((hF.const_mul z).exp.ennreal_ofReal) x
    ((hh.comp hs).comp (measurable_const.prodMk measurable_id))

def pathOneKernel : (n : ℕ) → (Fin n → Kernel X X) → Kernel X X
  | 0, _ => Kernel.id
  | n+1, κ => pathOneKernel n (fun i => κ i.succ) ∘ₖ κ 0

def pathPairKernel : (n : ℕ) → (Fin n → Kernel X X) → Fin (n+1) → Kernel X (X×X)
  | 0, _, _ => Kernel.deterministic (fun x => (x,x)) (measurable_id.prodMk measurable_id)
  | n+1, κ, d => Fin.cases
      (pathOneKernel (n+1) κ ×ₖ pathOneKernel (n+1) κ)
      (fun j => pathPairKernel n (fun i => κ i.succ) j ∘ₖ κ 0) d

lemma pathOneKernel_markov (n : ℕ) (κ : Fin n → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) : IsMarkovKernel (pathOneKernel n κ) := by
  induction n with
  | zero => dsimp [pathOneKernel]; infer_instance
  | succ n ih =>
    have := hκ 0
    have := ih (fun i => κ i.succ) (fun i => hκ i.succ)
    dsimp [pathOneKernel]; infer_instance

lemma pathPairKernel_markov (n : ℕ) (κ : Fin n → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (d : Fin (n+1)) :
    IsMarkovKernel (pathPairKernel n κ d) := by
  induction n with
  | zero => dsimp [pathPairKernel]; infer_instance
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) d
    · have := pathOneKernel_markov (n+1) κ hκ
      simp only [pathPairKernel,Fin.cases_zero]; infer_instance
    · have := hκ 0
      have := ih (fun i => κ i.succ) (fun i => hκ i.succ) j
      simp only [pathPairKernel,Fin.cases_succ]; infer_instance

lemma path_bounded_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

lemma bounded_probability_mean_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
  have hi := path_bounded_integrable μ f hf C hb
  have hs : Integrable (fun x => (f x)^2) μ :=
    path_bounded_integrable μ _ (hf.pow_const 2) (C^2) (fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hb x,abs_nonneg (f x),sq_abs (f x)])
  let m := ∫ x, f x ∂μ
  have he : (∫ x, (f x-m)^2 ∂μ) = (∫ x, (f x)^2 ∂μ)-m^2 := by
    calc
      _ = ∫ x, (f x)^2 - 2*m*f x + m^2 ∂μ := by congr 1; funext x; ring
      _ = (∫ x, (f x)^2 ∂μ) - 2*m*m + m^2 := by
        rw [integral_add (f := fun x => (f x)^2-2*m*f x) (g := fun _ => m^2)
          (hs.sub (hi.const_mul (2*m))) (integrable_const _),
          integral_sub (f := fun x => (f x)^2) (g := fun x => 2*m*f x) hs (hi.const_mul (2*m)),
          integral_const_mul,integral_const]
        simp [m]
      _ = _ := by ring
  have hn : 0 ≤ ∫ x, (f x-m)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  rw [he] at hn
  exact sub_nonneg.mp hn

def pathMean (n : ℕ) (κ : Fin n → Kernel X X) (f : X → ℝ) (x : X) : ℝ :=
  ∫ y, f y ∂pathOneKernel n κ x

def pathCorrelation (n : ℕ) (κ : Fin n → Kernel X X) (f : X → ℝ)
    (d : Fin (n+1)) (x : X) : ℝ :=
  ∫ y, f y.1*f y.2 ∂pathPairKernel n κ d x

lemma pathMean_measurable (n : ℕ) (κ : Fin n → Kernel X X)
    (f : X → ℝ) (hf : Measurable f) : Measurable (pathMean n κ f) :=
  hf.stronglyMeasurable.integral_kernel.measurable

lemma pathCorrelation_measurable (n : ℕ) (κ : Fin n → Kernel X X)
    (f : X → ℝ) (hf : Measurable f) (d : Fin (n+1)) :
    Measurable (pathCorrelation n κ f d) :=
  ((hf.comp measurable_fst).mul (hf.comp measurable_snd)).stronglyMeasurable.integral_kernel.measurable

lemma pathMean_bound (n : ℕ) (κ : Fin n → Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (f : X → ℝ) (C : ℝ) (hb : ∀ x, |f x| ≤ C) (x : X) : |pathMean n κ f x| ≤ C := by
  have := pathOneKernel_markov n κ hκ
  simpa [pathMean] using norm_integral_le_of_norm_le_const
    (μ := pathOneKernel n κ x) (f := f)
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

lemma pathCorrelation_bound (n : ℕ) (κ : Fin n → Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (f : X → ℝ) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C)
    (d : Fin (n+1)) (x : X) : |pathCorrelation n κ f d x| ≤ C^2 := by
  have := pathPairKernel_markov n κ hκ d
  have hb' (y : X×X) : ‖f y.1*f y.2‖ ≤ C^2 := by
    rw [Real.norm_eq_abs,abs_mul,pow_two]
    exact mul_le_mul (hb y.1) (hb y.2) (abs_nonneg _) hC
  simpa [pathCorrelation] using norm_integral_le_of_norm_le_const
    (μ := pathPairKernel n κ d x) (Filter.Eventually.of_forall hb')

lemma pathMean_succ (n : ℕ) (κ : Fin (n+1) → Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) (x : X) :
    pathMean (n+1) κ f x = ∫ y, pathMean n (fun i => κ i.succ) f y ∂κ 0 x := by
  have := hκ 0
  have := pathOneKernel_markov n (fun i => κ i.succ) (fun i => hκ i.succ)
  exact Kernel.integral_comp (path_bounded_integrable _ f hf C hb)

lemma pathCorrelation_zero (n : ℕ) (κ : Fin n → Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (f : X → ℝ) (hf : Measurable f) (x : X) :
    pathCorrelation n κ f 0 x = (pathMean n κ f x)^2 := by
  cases n with
  | zero =>
    simp only [pathCorrelation,pathPairKernel,Kernel.deterministic_apply,pathMean,pathOneKernel,
      Kernel.id_apply]
    rw [integral_dirac' (fun y : X×X => f y.1*f y.2) (x,x)
      (show StronglyMeasurable (fun y : X×X => f y.1*f y.2) from
        ((hf.comp measurable_fst).mul (hf.comp measurable_snd)).stronglyMeasurable),
      integral_dirac' _ _ hf.stronglyMeasurable,pow_two]
  | succ n =>
    have := pathOneKernel_markov (n+1) κ hκ
    simp only [pathCorrelation,pathPairKernel,Fin.cases_zero,Kernel.prod_apply]
    rw [integral_prod_mul]
    exact (pow_two _).symm

lemma pathCorrelation_succ (n : ℕ) (κ : Fin (n+1) → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (f : X → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) (d : Fin (n+1)) (x : X) :
    pathCorrelation (n+1) κ f d.succ x =
      ∫ y, pathCorrelation n (fun i => κ i.succ) f d y ∂κ 0 x := by
  have := hκ 0
  have := pathPairKernel_markov n (fun i => κ i.succ) (fun i => hκ i.succ) d
  simp only [pathCorrelation,pathPairKernel,Fin.cases_succ]
  apply Kernel.integral_comp
  apply path_bounded_integrable _ _ ((hf.comp measurable_fst).mul (hf.comp measurable_snd)) (C^2)
  intro y
  change |f y.1*f y.2| ≤ C^2
  rw [abs_mul,pow_two]
  exact mul_le_mul (hb y.1) (hb y.2) (abs_nonneg _) hC

lemma pathCorrelation_nonneg (n : ℕ) (κ : Fin n → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (f : X → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) (d : Fin (n+1)) (x : X) :
    0 ≤ pathCorrelation n κ f d x := by
  induction n generalizing x with
  | zero =>
    have hd : d=0 := by apply Fin.ext; omega
    rw [hd,pathCorrelation_zero _ _ hκ f hf]
    exact sq_nonneg _
  | succ n ih =>
    induction d using Fin.cases with
    | zero => rw [pathCorrelation_zero _ _ hκ f hf]; exact sq_nonneg _
    | succ d =>
      rw [pathCorrelation_succ n κ hκ f hf C hC hb d x]
      exact integral_nonneg (fun y => ih _ (fun i => hκ i.succ) d y)

lemma pathCorrelation_monotone (n : ℕ) (κ : Fin n → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (f : X → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) (x : X) :
    Monotone (fun d => pathCorrelation n κ f d x) := by
  induction n generalizing x with
  | zero => exact fun a b _ => le_of_eq (congrArg (fun d => pathCorrelation 0 κ f d x)
      (by apply Fin.ext; omega))
  | succ n ih =>
    have := hκ 0
    let κ' : Fin n → Kernel X X := fun i => κ i.succ
    have hκ' : ∀ i, IsMarkovKernel (κ' i) := fun i => hκ i.succ
    have hi (d : Fin (n+1)) : Integrable (pathCorrelation n κ' f d) (κ 0 x) :=
      path_bounded_integrable _ _ (pathCorrelation_measurable n κ' f hf d) (C^2)
        (fun y => pathCorrelation_bound n κ' hκ' f C hC hb d y)
    intro a b hab
    change pathCorrelation (n+1) κ f a x ≤ pathCorrelation (n+1) κ f b x
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact le_rfl
      | succ b =>
        rw [pathCorrelation_zero _ _ hκ f hf,pathMean_succ n κ hκ f hf C hb,
          pathCorrelation_succ n κ hκ f hf C hC hb]
        have hJ := bounded_probability_mean_sq (κ 0 x) (pathMean n κ' f)
          (pathMean_measurable n κ' f hf) C hC (pathMean_bound n κ' hκ' f C hb)
        apply hJ.trans
        have he : (fun y => (pathMean n κ' f y)^2) = pathCorrelation n κ' f 0 := by
          funext y; exact (pathCorrelation_zero n κ' hκ' f hf y).symm
        rw [he]
        exact integral_mono (hi 0) (hi b) (fun y => ih κ' hκ' y (Fin.zero_le b))
    | succ a =>
      induction b using Fin.cases with
      | zero => simp at hab
      | succ b =>
        rw [pathCorrelation_succ n κ hκ f hf C hC hb,
          pathCorrelation_succ n κ hκ f hf C hC hb]
        exact integral_mono (hi a) (hi b) (fun y => ih κ' hκ' y (Fin.succ_le_succ_iff.mp hab))

end SphericalPerceptronFreeEnergy
end

end OAI
