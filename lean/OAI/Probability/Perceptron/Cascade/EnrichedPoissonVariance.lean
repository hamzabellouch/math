import Mathlib
import OAI.Probability.Perceptron.Pressure.EnrichedPatternVariance
import OAI.Probability.Perceptron.Cascade.PoissonCountMoments
import OAI.Probability.Perceptron.Variational.CountMixtureVariance

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def infinitePatternRowsLaw (N : ℕ) : Measure (ℕ → Fin N → ℝ) :=
  Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin N => gaussianReal 0 1

instance (N : ℕ) : IsProbabilityMeasure (infinitePatternRowsLaw N) := by
  unfold infinitePatternRowsLaw
  infer_instance

def patternPrefix (N M : ℕ) (g : ℕ → Fin N → ℝ) : Fin M → Fin N → ℝ :=
  fun a => g a.val

lemma patternPrefix_measurable (N M : ℕ) : Measurable (patternPrefix N M) := by
  unfold patternPrefix
  fun_prop

lemma patternPrefix_measurePreserving (N M : ℕ) : MeasurePreserving (patternPrefix N M)
    (infinitePatternRowsLaw N) (finitePatternRowsLaw N M) := by
  refine ⟨patternPrefix_measurable N M,?_⟩
  change Measure.map (fun g : ℕ → Fin N → ℝ => fun a : Fin M => g a.val)
    (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin N => gaussianReal 0 1)=
    Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]

lemma normalizedPatternEnergy_prefix_succ (N M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : ℕ → Fin N → ℝ) (x : NormalizedSpin N) :
    |normalizedPatternEnergy N (M+1) f (patternPrefix N (M+1) g) x-
      normalizedPatternEnergy N M f (patternPrefix N M g) x| ≤ ‖f‖ := by
  unfold normalizedPatternEnergy
  rw [Fin.sum_univ_castSucc]
  simp only [patternPrefix,Fin.val_castSucc,Fin.val_last,add_sub_cancel_left]
  simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (∑ i, g M i*x.val i)

def enrichedPoissonLog (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ)
    (a : ℕ × ((ℕ → Fin (n+1) → ℝ) ×
      (EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k))) : ℝ :=
  enrichedCascadeLog n a.1 k f (patternPrefix (n+1) a.1 a.2.1) p d u h a.2.2

def enrichedRowsDisorderLaw (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) :=
  (infinitePatternRowsLaw (n+1)).prod (enrichedDisorderLaw n k p z)

instance (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) :
    IsProbabilityMeasure (enrichedRowsDisorderLaw n k p z) := by
  unfold enrichedRowsDisorderLaw
  infer_instance

lemma enrichedPoissonLog_measurable (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) :
    Measurable (enrichedPoissonLog n k f p d u h) := by
  apply measurable_from_prod_countable_right
  intro M
  have hh := (enrichedCascadeLog_parameters_measurable n M k f p d u h z).comp
    (((patternPrefix_measurable (n+1) M).comp
      (measurable_fst (α := ℕ → Fin (n+1) → ℝ)
        (β := EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k))).prodMk measurable_snd)
  simpa only [enrichedPoissonLog,Function.comp_def] using hh

lemma enrichedPoissonLog_section_variance (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    MemLp (fun a => enrichedPoissonLog n k f p d u h (M,a)) 2 (enrichedRowsDisorderLaw n k p z) ∧
      variance (fun a => enrichedPoissonLog n k f p d u h (M,a)) (enrichedRowsDisorderLaw n k p z) ≤
      cascadeLogFluctuationConstant k z+(Real.pi^2/8)*
        ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2+(M:ℝ)*(2*‖f‖)^2 := by
  let E := EnrichedMark (n+1) (n+1) p
  let D := E × DecoratedCascade E k
  have hp : MeasurePreserving (fun a : (ℕ → Fin (n+1) → ℝ) × D =>
      (patternPrefix (n+1) M a.1,a.2))
      ((infinitePatternRowsLaw (n+1)).prod (enrichedDisorderLaw n k p z))
      ((finitePatternRowsLaw (n+1) M).prod (enrichedDisorderLaw n k p z)) :=
    (patternPrefix_measurePreserving (n+1) M).prod
      (MeasurePreserving.id (enrichedDisorderLaw n k p z))
  have hs := enrichedFixedCountLog_variance n M k f p d u h z hz hz0 hz1
  have hl := hs.1.comp_measurePreserving hp
  have hv := (hp.variance_fun_comp hs.1.aestronglyMeasurable.aemeasurable).trans_le hs.2
  constructor
  · simpa only [Function.comp_def,enrichedFixedCountLog,enrichedPoissonLog,enrichedRowsDisorderLaw] using hl
  · simpa only [enrichedFixedCountLog,enrichedPoissonLog,enrichedRowsDisorderLaw] using hv

lemma enrichedPoissonLog_mean_succ (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (M : ℕ) :
    |(∫ a, enrichedPoissonLog n k f p d u h (M+1,a) ∂enrichedRowsDisorderLaw n k p z)-
      ∫ a, enrichedPoissonLog n k f p d u h (M,a) ∂enrichedRowsDisorderLaw n k p z| ≤ ‖f‖ := by
  let μ := infinitePatternRowsLaw (n+1)
  let G (M : ℕ) := fun g => enrichedExpectedLog n M k f p d u h z (patternPrefix (n+1) M g)
  have hG (M : ℕ) : MemLp (G M) 2 μ :=
    (enrichedExpectedLog_memLp n M k f p d u h z hz hz0 hz1).comp_measurePreserving
      (patternPrefix_measurePreserving (n+1) M)
  have he (M : ℕ) : (∫ a, enrichedPoissonLog n k f p d u h (M,a) ∂enrichedRowsDisorderLaw n k p z)=
      ∫ g, G M g ∂μ :=
    integral_prod _ ((enrichedPoissonLog_section_variance n M k f p d u h z hz hz0 hz1).1.integrable (by norm_num))
  rw [he,he,← integral_sub ((hG (M+1)).integrable (by norm_num)) ((hG M).integrable (by norm_num))]
  have hh (g) : |G (M+1) g-G M g| ≤ ‖f‖ :=
    enrichedExpectedLog_pattern_change n (M+1) M k f _ _ p d u h z hz hz0 hz1
      (normalizedPatternEnergy_prefix_succ (n+1) M f g)
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (f := fun g => G (M+1) g-G M g)
    (ae_of_all _ hh)

lemma enrichedPoissonLog_variance (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (r : ℝ≥0) :
    let μ := (poissonMeasure r).prod (enrichedRowsDisorderLaw n k p z)
    MemLp (enrichedPoissonLog n k f p d u h) 2 μ ∧
      variance (enrichedPoissonLog n k f p d u h) μ ≤
      cascadeLogFluctuationConstant k z+(Real.pi^2/8)*
        ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2+
          (r:ℝ)*(2*‖f‖)^2+‖f‖^2*((r:ℝ)+1) := by
  let ν := enrichedRowsDisorderLaw n k p z
  let F := enrichedPoissonLog n k f p d u h
  let G := fun M => ∫ a, F (M,a) ∂ν
  let K := cascadeLogFluctuationConstant k z+(Real.pi^2/8)*
        ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2
  let A := fun M : ℕ => K+(M:ℝ)*(2*‖f‖)^2
  have hGdiff := enrichedPoissonLog_mean_succ n k f p d u h z hz hz0 hz1
  have hG : MemLp G 2 (poissonMeasure r) := poisson_bounded_increment_memLp r (norm_nonneg f) hGdiff
  have hAi : Integrable A (poissonMeasure r) :=
    (integrable_const K).add ((poisson_nat_memLp r).integrable (by norm_num) |>.mul_const _)
  have hs (M) := enrichedPoissonLog_section_variance n M k f p d u h z hz hz0 hz1
  have hp : MemLp F 2 ((poissonMeasure r).prod ν) :=
    memLp_prod_of_conditional_square_function (poissonMeasure r) ν
      (enrichedPoissonLog_measurable n k f p d u h z) hG hAi (fun M => (hs M).1)
      (fun M => by
        have hv := (hs M).2
        rw [variance_eq_integral (hs M).1.aestronglyMeasurable.aemeasurable] at hv
        exact hv)
  refine ⟨hp,?_⟩
  have hv := variance_prod_le_integral (poissonMeasure r) ν hp (fun M => (hs M).1) hG hAi
    (fun M => (hs M).2) (poisson_bounded_increment_variance r (norm_nonneg f) hGdiff)
  have he : (∫ M, A M ∂poissonMeasure r)=K+(r:ℝ)*(2*‖f‖)^2 := by
    rw [integral_add (integrable_const K) ((poisson_nat_memLp r).integrable (by norm_num) |>.mul_const _)]
    simp only [integral_const,integral_mul_const,poisson_nat_mean]
    simp
  rw [he] at hv
  exact hv

end SphericalPerceptronFreeEnergy
end

end OAI
