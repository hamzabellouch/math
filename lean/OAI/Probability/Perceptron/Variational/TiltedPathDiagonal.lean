import Mathlib
import OAI.Probability.Perceptron.Pressure.IndexedTerminalProduct

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
variable {X Y R Q : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace R] [MeasurableSpace Q]

lemma pathCorrelation_last (n : ℕ) (κ : Fin n → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (f : X → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) (x : X) :
    pathCorrelation n κ f (Fin.last n) x = pathMean n κ (fun y => (f y)^2) x := by
  have hsB : ∀ y, |(f y)^2| ≤ C^2 := fun y => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb y) 2
  induction n generalizing x with
  | zero =>
    simp only [pathCorrelation,pathPairKernel,Kernel.deterministic_apply,pathMean,pathOneKernel,Kernel.id_apply]
    rw [integral_dirac' (fun y : X × X => f y.1*f y.2) (x,x) ((hf.comp measurable_fst).mul (hf.comp measurable_snd)).stronglyMeasurable,
      integral_dirac' (fun y => (f y)^2) x (hf.pow_const 2).stronglyMeasurable,pow_two]
  | succ n ih =>
    rw [show Fin.last (n+1) = (Fin.last n).succ from rfl,
      pathCorrelation_succ n κ hκ f hf C hC hb,
      pathMean_succ n κ hκ _ (hf.pow_const 2) (C^2) hsB]
    apply integral_congr_ae
    exact ae_of_all _ fun y => ih _ (fun i => hκ i.succ) y

lemma pathCorrelation_le_diagonal (n : ℕ) (κ : Fin n → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0 ≤ C) (hfB : ∀ x, |f x| ≤ C) (hgB : ∀ x, |g x| ≤ D)
    (hfg : ∀ x, (f x)^2 ≤ g x) (d : Fin (n+1)) (x : X) :
    pathCorrelation n κ f d x ≤ pathMean n κ g x := by
  apply (pathCorrelation_monotone n κ hκ f hf C hC hfB x (Fin.le_last d)).trans
  change pathCorrelation n κ f (Fin.last n) x ≤ _
  rw [pathCorrelation_last n κ hκ f hf C hC hfB x]
  have := pathOneKernel_markov n κ hκ
  apply integral_mono
  · apply path_bounded_integrable _ _ (hf.pow_const 2) (C^2)
    intro y; rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hfB y) 2
  · exact path_bounded_integrable _ g hg D hgB
  · exact hfg

def rootPathCorrelation (μ : Measure R) (x : R→X) (n : ℕ) (κ : Fin n→Kernel X X)
    (f : X→ℝ) (d : Fin (n+1)) : ℝ := ∫ r, pathCorrelation n κ f d (x r) ∂μ

def rootPathMean (μ : Measure R) (x : R→X) (n : ℕ) (κ : Fin n→Kernel X X)
    (f : X→ℝ) : ℝ := ∫ r, pathMean n κ f (x r) ∂μ

lemma rootPathCorrelation_integrable (μ : Measure R) [IsFiniteMeasure μ]
    (x : R→X) (hx : Measurable x) (n : ℕ) (κ : Fin n→Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (f : X→ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0≤C) (hb : ∀ y, |f y|≤C) (d : Fin (n+1)) :
    Integrable (fun r => pathCorrelation n κ f d (x r)) μ :=
  path_bounded_integrable μ _ ((pathCorrelation_measurable n κ f hf d).comp hx)
    (C^2) (fun r => pathCorrelation_bound n κ hκ f C hC hb d (x r))

lemma rootPathCorrelation_nonneg (μ : Measure R) (x : R→X)
    (n : ℕ) (κ : Fin n→Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (f : X→ℝ) (hf : Measurable f) (C : ℝ) (hC : 0≤C) (hb : ∀ y, |f y|≤C)
    (d : Fin (n+1)) : 0≤rootPathCorrelation μ x n κ f d :=
  integral_nonneg fun r => pathCorrelation_nonneg n κ hκ f hf C hC hb d (x r)

lemma rootPathCorrelation_monotone (μ : Measure R) [IsFiniteMeasure μ]
    (x : R→X) (hx : Measurable x) (n : ℕ) (κ : Fin n→Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (f : X→ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0≤C) (hb : ∀ y, |f y|≤C) :
    Monotone (rootPathCorrelation μ x n κ f) := by
  intro i j hij
  exact integral_mono (rootPathCorrelation_integrable μ x hx n κ hκ f hf C hC hb i)
    (rootPathCorrelation_integrable μ x hx n κ hκ f hf C hC hb j)
    (fun r => pathCorrelation_monotone n κ hκ f hf C hC hb (x r) hij)

lemma rootPathCorrelation_bound (μ : Measure R) [IsProbabilityMeasure μ]
    (x : R→X) (n : ℕ) (κ : Fin n→Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (f : X→ℝ) (C : ℝ) (hC : 0≤C) (hb : ∀ y, |f y|≤C) (d : Fin (n+1)) :
    |rootPathCorrelation μ x n κ f d|≤C^2 := by
  simpa only [rootPathCorrelation,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=μ) (f:=fun r => pathCorrelation n κ f d (x r))
      (ae_of_all _ fun r => by
        simpa only [Real.norm_eq_abs] using (pathCorrelation_bound n κ hκ f C hC hb d (x r)))

lemma rootPathCorrelation_le_diagonal (μ : Measure R) [IsFiniteMeasure μ]
    (x : R→X) (hx : Measurable x) (n : ℕ) (κ : Fin n→Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (f g : X→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hfB : ∀ y, |f y|≤C) (hgB : ∀ y, |g y|≤D)
    (hfg : ∀ y, (f y)^2≤g y) (d : Fin (n+1)) :
    rootPathCorrelation μ x n κ f d≤rootPathMean μ x n κ g := by
  apply integral_mono (rootPathCorrelation_integrable μ x hx n κ hκ f hf C hC hfB d)
    (path_bounded_integrable μ _ ((pathMean_measurable n κ g hg).comp hx) D
      (fun r => pathMean_bound n κ hκ g D hgB (x r)))
  exact fun r => pathCorrelation_le_diagonal n κ hκ f g hf hg C D hC hfB hgB hfg d (x r)

lemma rootPathCorrelation_one (μ : Measure R) [IsProbabilityMeasure μ]
    (x : R→X) (n : ℕ) (κ : Fin n→Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (d : Fin (n+1)) : rootPathCorrelation μ x n κ (fun _=>1) d=1 := by
  simp only [rootPathCorrelation,pathCorrelation_one n κ hκ,integral_const,probReal_univ,one_smul]

lemma rootPathCorrelation_parallel (μ : Measure R) (σ : Measure Q) [SFinite μ] [SFinite σ]
    (x : R→X) (y : Q→Y) (n : ℕ) (κ : Fin n→Kernel X X) (η : Fin n→Kernel Y Y)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (hη : ∀ i, IsMarkovKernel (η i))
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ a, |f a|≤C) (hgB : ∀ b, |g b|≤D)
    (d : Fin (n+1)) :
    rootPathCorrelation (μ.prod σ) (fun p => (x p.1,y p.2)) n (fun i => κ i ∥ₖ η i)
      (fun p => f p.1*g p.2) d =
      rootPathCorrelation μ x n κ f d * rootPathCorrelation σ y n η g d := by
  unfold rootPathCorrelation
  simp_rw [pathCorrelation_parallel n κ η hκ hη f g hf hg C D hC hD hfB hgB]
  exact integral_prod_mul (fun r => pathCorrelation n κ f d (x r))
    (fun q => pathCorrelation n η g d (y q))

open scoped ENNReal NNReal BoundedContinuousFunction

def residualResponse (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : ℝ) : ℝ :=
  gaussianAverage s (expBCF 1 f * v) x / gaussianAverage s (expBCF 1 f) x

lemma residualResponse_eq_tiltMean (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : ℝ) :
    residualResponse s f v x =
      tiltMean (gaussianReal 0 s) (fun z => f (x+z)) (fun z => v (x+z)) 1 := by
  simp only [residualResponse,gaussianAverage,tiltMean,tiltIntegral,tiltPartition,
    Pi.mul_apply,expBCF_apply,one_mul]

lemma residualResponse_continuous (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) :
    Continuous (residualResponse s f v) :=
  (gaussianAverage_continuous s (expBCF 1 f*v)).div
    (gaussianAverage_continuous s (expBCF 1 f))
    (fun x => (gaussianAverage_exp_pos s 1 f x).ne')

lemma residualResponse_bound (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : ℝ) :
    |residualResponse s f v x|≤‖v‖ := by
  rw [residualResponse_eq_tiltMean]
  exact tilt_mean_bound (gaussianReal 0 s) (f.measurable.comp (measurable_const.add measurable_id))
    (v.measurable.comp (measurable_const.add measurable_id)) (norm_nonneg _) (norm_nonneg _)
    (fun z => f.norm_coe_le_norm (x+z)) (fun z => v.norm_coe_le_norm (x+z)) 1

def residualResponseBCF (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨residualResponse s f v,residualResponse_continuous s f v⟩
    (2*‖v‖) (by
      intro x y
      change |residualResponse s f v x-residualResponse s f v y|≤2*‖v‖
      exact (abs_sub _ _).trans (by
        linarith [residualResponse_bound s f v x, residualResponse_bound s f v y]))

@[simp] lemma residualResponseBCF_apply (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : ℝ) :
    residualResponseBCF s f v x=residualResponse s f v x := rfl

lemma residualResponse_weighted (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s (expBCF 1 f) x * residualResponse s f v x =
      gaussianAverage s (expBCF 1 f*v) x := by
  unfold residualResponse
  exact mul_div_cancel₀ _ (gaussianAverage_exp_pos s 1 f x).ne'

lemma residualResponse_jensen (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : ℝ) :
    (residualResponse s f v x)^2≤residualResponse s f (v*v) x := by
  have hH : Measurable (fun z => f (x+z)) := f.measurable.comp (measurable_const.add measurable_id)
  have hV : Measurable (fun z => v (x+z)) := v.measurable.comp (measurable_const.add measurable_id)
  have := tilt_law_probability (gaussianReal 0 s) hH (norm_nonneg f)
    (fun z => f.norm_coe_le_norm (x+z)) 1
  let μ := tiltLaw (gaussianReal 0 s) (fun z => f (x+z)) 1
  have hLp : MemLp (fun z => v (x+z)) 2 μ :=
    MemLp.of_bound hV.aestronglyMeasurable ‖v‖ (ae_of_all _ fun z => v.norm_coe_le_norm (x+z))
  have h := variance_nonneg (fun z => v (x+z)) μ
  rw [variance_eq_sub hLp] at h
  simp only [Pi.pow_apply] at h
  have hsq : (∫ z, v (x+z) ∂μ)^2≤∫ z, (v (x+z))^2 ∂μ := sub_nonneg.mp h
  simp only [μ,tilt_law_integral (gaussianReal 0 s) hH (norm_nonneg f)
    (fun z => f.norm_coe_le_norm (x+z)) 1,←residualResponse_eq_tiltMean] at hsq
  simpa only [residualResponse_eq_tiltMean,BoundedContinuousFunction.mul_apply,pow_two] using hsq

lemma residualResponse_one (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    residualResponse s f 1 x=1 := by
  change gaussianAverage s (expBCF 1 f * 1 : ℝ →ᵇ ℝ) x / _=1
  rw [mul_one]
  exact div_self (gaussianAverage_exp_pos s 1 f x).ne'

end SphericalPerceptronFreeEnergy
end

end OAI
