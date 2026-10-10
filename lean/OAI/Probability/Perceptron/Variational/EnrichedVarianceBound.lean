import Mathlib
import OAI.Probability.Perceptron.Variational.EnrichedUniformBounds
import OAI.Probability.Perceptron.Cascade.EnrichedPoissonVariance

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def enrichedRandomPressure (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) :=
  fun a => (1/(n+1:ℕ))*enrichedPoissonLog n k f p d u h a

def enrichedPoissonDisorderLaw (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) (t : ℝ≥0) :=
  (poissonMeasure ((n+1:ℕ)*t)).prod (enrichedRowsDisorderLaw n k p z)

instance (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) (t : ℝ≥0) :
    IsProbabilityMeasure (enrichedPoissonDisorderLaw n k p z t) := by
  unfold enrichedPoissonDisorderLaw
  infer_instance

def enrichedVarianceConstant (k : ℕ) (z : Fin k → ℝ) (f : ℝ →ᵇ ℝ) (H T : ℝ) : ℝ :=
  max (cascadeLogFluctuationConstant k z) 0+(Real.pi^2/8)*5*(2*H+1)+
    5*T*‖f‖^2+‖f‖^2

lemma enrichedRandomPressure_variance (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (hu : ∀ j, u j ∈ Icc 1 2) {H T : ℝ} (hH : 0 ≤ H) (hh : h 0 ≤ H)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ T) :
    let μ := enrichedPoissonDisorderLaw n k p z t
    MemLp (enrichedRandomPressure n k f p d u h) 2 μ ∧
      variance (enrichedRandomPressure n k f p d u h) μ ≤
        enrichedVarianceConstant k z f H T/(n+1:ℕ) := by
  let N : ℝ := (n+1:ℕ)
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hN0 : 0<N := by linarith
  have hNne : N≠0 := ne_of_gt hN0
  have hp := enrichedPoissonLog_variance n k f p d u h z hz hz0 hz1 ((n+1:ℕ)*t)
  refine ⟨hp.1.const_mul (1/N),?_⟩
  have hroot := enrichedRootMap_norm_le p d h hH hh
  have hroot2 : ‖enrichedRootMap p d h‖^2 ≤ 2*H+1 := by
    have he := pow_le_pow_left₀ (norm_nonneg _) hroot 2
    rwa [Real.sq_sqrt (by positivity)] at he
  have hfeat := enrichedFeatureBound_sq_le (n+1) (by omega) u hu
  have hprod : ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2 ≤
      5*N*(2*H+1) := by
    rw [mul_pow]
    exact mul_le_mul hfeat hroot2 (sq_nonneg _) (by positivity)
  have hk : cascadeLogFluctuationConstant k z ≤ max (cascadeLogFluctuationConstant k z) 0*N :=
    (le_max_left _ _).trans (le_mul_of_one_le_right (le_max_right _ _) hN)
  have hfloor := mul_le_mul_of_nonneg_left ht hN0.le
  have hvar : variance (enrichedPoissonLog n k f p d u h)
      (enrichedPoissonDisorderLaw n k p z t) ≤ enrichedVarianceConstant k z f H T*N := by
    have hv := hp.2
    simp only [NNReal.coe_mul,NNReal.coe_natCast] at hv
    have hq := mul_le_mul_of_nonneg_left hprod (show (0:ℝ) ≤ Real.pi^2/8 by positivity)
    have htq := mul_le_mul_of_nonneg_right hfloor (show 0 ≤ 5*‖f‖^2 by positivity)
    have hfN := mul_le_mul_of_nonneg_left hN (sq_nonneg ‖f‖)
    change variance (enrichedPoissonLog n k f p d u h)
      ((poissonMeasure ((n+1:ℕ)*t)).prod (enrichedRowsDisorderLaw n k p z)) ≤ _
    dsimp only [enrichedVarianceConstant]
    change variance (enrichedPoissonLog n k f p d u h) _ ≤ _ at hv
    change variance (enrichedPoissonLog n k f p d u h) _ ≤
      cascadeLogFluctuationConstant k z + Real.pi^2/8*
        ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2+
        (N*(t:ℝ))*(2*‖f‖)^2+‖f‖^2*(N*(t:ℝ)+1) at hv
    nlinarith
  change variance (fun a => (1/N)*enrichedPoissonLog n k f p d u h a)
    (enrichedPoissonDisorderLaw n k p z t) ≤ enrichedVarianceConstant k z f H T/N
  rw [variance_const_mul]
  calc
    _ ≤ (1/N)^2*(enrichedVarianceConstant k z f H T*N) :=
      mul_le_mul_of_nonneg_left hvar (sq_nonneg (1/N))
    _ = _ := by field_simp

lemma enrichedRandomPressure_centered_square (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (hu : ∀ j, u j ∈ Icc 1 2) {H T : ℝ} (hH : 0 ≤ H) (hh : h 0 ≤ H)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ T) :
    let μ := enrichedPoissonDisorderLaw n k p z t
    let P := enrichedRandomPressure n k f p d u h
    (∫ a, |P a-∫ b, P b ∂μ|^2 ∂μ) ≤ enrichedVarianceConstant k z f H T/(n+1:ℕ) := by
  have hv := enrichedRandomPressure_variance n k f p d u h z hz hz0 hz1 hu hH hh t ht
  have hh := hv.2
  rw [variance_eq_integral hv.1.aestronglyMeasurable.aemeasurable] at hh
  simpa only [sq_abs] using hh

def sourceCascadeRealization (n k : ℕ) (p : Fin (n+1) → ℕ)
    (a : IndexedCascadeBase k × (ℕ → ℝ)) :=
  ((indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) a.2).1,
    indexedCascadeRealize k (a.1,(indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) a.2).2))

lemma sourceCascadeRealization_measurable (n k : ℕ) (p : Fin (n+1) → ℕ) :
    Measurable (sourceCascadeRealization n k p) := by
  unfold sourceCascadeRealization
  exact ((indexedGaussianDisorder_measurable k _).comp measurable_snd).fst.prodMk
    ((indexedCascadeRealize_measurable k).comp
      (measurable_fst.prodMk ((indexedGaussianDisorder_measurable k _).comp measurable_snd).snd))

lemma sourceCascadeRealization_preserving (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) :
    MeasurePreserving (sourceCascadeRealization n k p)
      ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)
      (enrichedDisorderLaw n k p z) := by
  let E := EnrichedMark (n+1) (n+1) p
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  let R := stdGaussian E
  let M := (indexedCascadeMarksLaw (gaussianMarkLaw (E := E)) k : Measure (IndexedCascadeMarks E k))
  have hg : MeasurePreserving (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p))
      countableGaussianLaw (R.prod M) :=
    ⟨indexedGaussianDisorder_measurable k _,indexedGaussianDisorder_law k _⟩
  have hr : MeasurePreserving (fun a : IndexedCascadeBase k × (E × IndexedCascadeMarks E k) =>
      (a.2.1,(a.1,a.2.2))) (B.prod (R.prod M)) (R.prod (B.prod M)) :=
    ⟨by fun_prop,prod_rotate_front B R M⟩
  have hc : MeasurePreserving (indexedCascadeRealize (S := E) k) (B.prod M)
      (decoratedCascadeLaw (gaussianMarkLaw (E := E)) k z) :=
    ⟨indexedCascadeRealize_measurable k,indexedCascadeRealize_law _ k z⟩
  exact (((MeasurePreserving.id R).prod hc).comp hr).comp ((MeasurePreserving.id B).prod hg)

abbrev SourceIndexedDisorder (n k : ℕ) :=
  ℕ × ((ℕ → Fin (n+1) → ℝ) × (IndexedCascadeBase k × (ℕ → ℝ)))

def sourceIndexedDisorderLaw (n k : ℕ) (z : Fin k → ℝ) (t : ℝ≥0) :
    Measure (SourceIndexedDisorder n k) :=
  (poissonMeasure ((n+1:ℕ)*t)).prod ((infinitePatternRowsLaw (n+1)).prod
    ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw))

instance (n k : ℕ) (z : Fin k → ℝ) (t : ℝ≥0) :
    IsProbabilityMeasure (sourceIndexedDisorderLaw n k z t) := by
  unfold sourceIndexedDisorderLaw
  infer_instance

def sourceDisorderRealization (n k : ℕ) (p : Fin (n+1) → ℕ) :
    SourceIndexedDisorder n k → ℕ × ((ℕ → Fin (n+1) → ℝ) ×
      (EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k)) :=
  Prod.map id (Prod.map id (sourceCascadeRealization n k p))

lemma sourceDisorderRealization_preserving (n k : ℕ) (p : Fin (n+1) → ℕ)
    (z : Fin k → ℝ) (t : ℝ≥0) :
    MeasurePreserving (sourceDisorderRealization n k p) (sourceIndexedDisorderLaw n k z t)
      (enrichedPoissonDisorderLaw n k p z t) :=
  (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod
    (sourceCascadeRealization_preserving n k p z))

def sourceIndexedPressure (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) : SourceIndexedDisorder n k → ℝ :=
  enrichedRandomPressure n k f p d u h ∘ sourceDisorderRealization n k p

lemma sourceIndexedPressure_memLp (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    MemLp (sourceIndexedPressure n k f p d u h) 2 (sourceIndexedDisorderLaw n k z t) := by
  have hp := (enrichedPoissonLog_variance n k f p d u h z hz hz0 hz1 ((n+1:ℕ)*t)).1
  exact (hp.const_mul (1/(n+1:ℕ))).comp_measurePreserving
    (sourceDisorderRealization_preserving n k p z t)

lemma sourceIndexedPressure_variance (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (hu : ∀ j, u j ∈ Icc 1 2) {H T : ℝ} (hH : 0 ≤ H) (hh : h 0 ≤ H)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ T) :
    variance (sourceIndexedPressure n k f p d u h) (sourceIndexedDisorderLaw n k z t) ≤
      enrichedVarianceConstant k z f H T/(n+1:ℕ) := by
  have hv := enrichedRandomPressure_variance n k f p d u h z hz hz0 hz1 hu hH hh t ht
  rw [sourceIndexedPressure, Function.comp_def,
    (sourceDisorderRealization_preserving n k p z t).variance_fun_comp hv.1.aestronglyMeasurable.aemeasurable]
  exact hv.2

end SphericalPerceptronFreeEnergy

end

end OAI
