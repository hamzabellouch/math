import Mathlib
import OAI.Probability.Perceptron.Interpolation.ReplicaIBP
import OAI.Probability.Perceptron.Variational.EnrichedVarianceBound
import OAI.Probability.Perceptron.Variational.UnboundedContact

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

abbrev SourceBaseData (n k : ℕ) := ℕ × ((ℕ → Fin (n+1) → ℝ) × IndexedCascadeBase k)

def sourceBaseDataLaw (n k : ℕ) (z : Fin k → ℝ) (t : ℝ≥0) : Measure (SourceBaseData n k) :=
  (poissonMeasure ((n+1:ℕ)*t)).prod ((infinitePatternRowsLaw (n+1)).prod
    (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)))

instance (n k : ℕ) (z : Fin k → ℝ) (t : ℝ≥0) : IsProbabilityMeasure (sourceBaseDataLaw n k z t) := by
  unfold sourceBaseDataLaw
  infer_instance

def sourceDisorderReassoc (n k : ℕ) (a : SourceBaseData n k × (ℕ → ℝ)) : SourceIndexedDisorder n k :=
  (a.1.1,(a.1.2.1,(a.1.2.2,a.2)))

lemma sourceDisorderReassoc_preserving (n k : ℕ) (z : Fin k → ℝ) (t : ℝ≥0) :
    MeasurePreserving (sourceDisorderReassoc n k)
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) (sourceIndexedDisorderLaw n k z t) := by
  let K := poissonMeasure ((n+1:ℕ)*t)
  let R := infinitePatternRowsLaw (n+1)
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  exact ((MeasurePreserving.id K).prod (measurePreserving_prodAssoc R B countableGaussianLaw)).comp
    (measurePreserving_prodAssoc K (R.prod B) countableGaussianLaw)

def indexedLeafKernel (k : ℕ) : Kernel (IndexedCascadeBase k) (IndexedLeaf k) :=
  ⟨indexedLeafProbability k,indexedLeafProbability_measurable k⟩

instance (k : ℕ) : IsMarkovKernel (indexedLeafKernel k) := ⟨fun b => indexedLeafProbability_isProbability k b⟩

def sourceSpinLeafKernel (n k : ℕ) : Kernel (SourceBaseData n k) (NormalizedSpin (n+1) × IndexedLeaf k) :=
  (Kernel.const _ (unitSphereLaw (n+1))).prod
    ((indexedLeafKernel k).comap
      (fun a : SourceBaseData n k => a.2.2) (by fun_prop))

lemma sourceSpinLeafKernel_apply (n k : ℕ) (a : SourceBaseData n k) :
    sourceSpinLeafKernel n k a = enrichedIndexedBaseMeasure n k a.2.2 := by
  rw [sourceSpinLeafKernel,Kernel.prod_apply]
  rfl

instance (n k : ℕ) : IsMarkovKernel (sourceSpinLeafKernel n k) := by
  constructor
  intro a
  rw [sourceSpinLeafKernel_apply]
  infer_instance

def sourceBaseEnergy (n k : ℕ) (f : ℝ →ᵇ ℝ) (h : Fin (k+1) → ℝ)
    (a : SourceBaseData n k) : NormalizedSpin (n+1) × IndexedLeaf k → ℝ :=
  enrichedIndexedBoundedEnergy n a.1 k f (patternPrefix (n+1) a.1 a.2.1) h

lemma sourceBaseEnergy_measurable (n k : ℕ) (f : ℝ →ᵇ ℝ) (h : Fin (k+1) → ℝ) :
    Measurable (Function.uncurry (sourceBaseEnergy n k f h)) := by
  have hm : Measurable (fun a : ℕ × (((ℕ → Fin (n+1) → ℝ) × IndexedCascadeBase k) ×
      (NormalizedSpin (n+1) × IndexedLeaf k)) =>
      sourceBaseEnergy n k f h (a.1,a.2.1) a.2.2) := by
    apply measurable_from_prod_countable_right
    intro M
    exact ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp
      (((patternPrefix_measurable (n+1) M).comp measurable_fst.fst).prodMk measurable_snd.fst)).sub measurable_const
  exact hm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

lemma sourceBaseData_regular (n k : ℕ) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    ∀ᵐ a ∂sourceBaseDataLaw n k z t, IndexedCascadeGood k a.2.2 ∧
      0 < ((indexedLeafMeasure k a.2.2) univ).toReal := by
  have hp : MeasurePreserving (fun a : SourceBaseData n k => a.2.2)
      (sourceBaseDataLaw n k z t) (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) :=
    measurePreserving_snd.comp measurePreserving_snd
  exact hp.quasiMeasurePreserving.ae ((indexedCascadeGood_ae k z hz0 hz1).and
    (indexedLeafMeasure_regular k z hz hz0 hz1))

def sourceKernelPressure (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ)
    (a : SourceBaseData n k × (ℕ → ℝ)) : ℝ :=
  (1/(n+1:ℕ))*Real.log (tiltPartition (sourceSpinLeafKernel n k a.1)
    (enrichedIndexedHamiltonian n a.1.1 k f (patternPrefix (n+1) a.1.1 a.1.2.1) p d h u a.2) 1)

lemma sourceKernelPressure_eq (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (a : SourceBaseData n k × (ℕ → ℝ))
    (ha : IndexedCascadeGood k a.1.2.2) (ha' : 0 < ((indexedLeafMeasure k a.1.2.2) univ).toReal)
    (u : Fin (n+1) → ℝ) :
    sourceKernelPressure n k f p d u h a = sourceIndexedPressure n k f p d u h (sourceDisorderReassoc n k a) := by
  rw [sourceKernelPressure,sourceSpinLeafKernel_apply,enrichedIndexedHamiltonian_partition _ _ _ _ _ _ _ _ _ _ _ ha ha']
  rfl

lemma sourceKernelPressure_ae (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw, ∀ u,
      sourceKernelPressure n k f p d u h a = sourceIndexedPressure n k f p d u h (sourceDisorderReassoc n k a) := by
  filter_upwards [(measurePreserving_fst (μ := sourceBaseDataLaw n k z t)
    (ν := countableGaussianLaw)).quasiMeasurePreserving.ae (sourceBaseData_regular n k z hz hz0 hz1 t)] with a ha u
  exact sourceKernelPressure_eq n k f p d h a ha.1 ha.2 u

lemma sourceKernelPressure_memLp (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    MemLp (sourceKernelPressure n k f p d u h) 2 ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) := by
  have hl := (sourceIndexedPressure_memLp n k f p d u h z hz hz0 hz1 t).comp_measurePreserving
    (sourceDisorderReassoc_preserving n k z t)
  apply hl.ae_eq
  exact (sourceKernelPressure_ae n k f p d h z hz hz0 hz1 t).mono fun a ha => (ha u).symm

lemma sourceKernelPressure_variance (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (hu : ∀ j, u j ∈ Icc 1 2)
    {H T : ℝ} (hH : 0 ≤ H) (hh : h 0 ≤ H) (t : ℝ≥0) (ht : (t:ℝ) ≤ T) :
    variance (sourceKernelPressure n k f p d u h) ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) ≤
      enrichedVarianceConstant k z f H T/(n+1:ℕ) := by
  have he := (sourceKernelPressure_ae n k f p d h z hz hz0 hz1 t).mono fun a ha => ha u
  rw [variance_congr he]
  have hl := sourceIndexedPressure_memLp n k f p d u h z hz hz0 hz1 t
  rw [(sourceDisorderReassoc_preserving n k z t).variance_fun_comp hl.aestronglyMeasurable.aemeasurable]
  exact sourceIndexedPressure_variance n k f p d u h z hz hz0 hz1 hu hH hh t ht

lemma measurable_disorder_state_lift {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
    {F : (ℕ → ℝ) → S → ℝ} (hF : Measurable (Function.uncurry F)) :
    Measurable (fun a : (A × (ℕ → ℝ)) × S => F a.1.2 a.2) :=
  hF.comp (measurable_fst.snd.prodMk measurable_snd)

def sourceCouplingHamiltonian (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (a : SourceBaseData n k × (ℕ → ℝ)) :=
  enrichedIndexedHamiltonian n a.1.1 k f (patternPrefix (n+1) a.1.1 a.1.2.1) p d h u a.2

def sourceCouplingEnergy (n k : ℕ) (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (j : Fin (n+1)) (a : SourceBaseData n k × (ℕ → ℝ))
    (x : NormalizedSpin (n+1) × IndexedLeaf k) :=
  perturbationAmplitude (n+1) (fun _ => 1) j*
    countableGaussianField (sourceGaussianTestRow p d h j)
      (indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) k) a.2 x

lemma sourceCouplingBase_measurable (n k : ℕ) (f : ℝ →ᵇ ℝ) (h : Fin (k+1) → ℝ) :
    Measurable (fun a : (SourceBaseData n k × (ℕ → ℝ)) ×
      (NormalizedSpin (n+1) × IndexedLeaf k) => sourceBaseEnergy n k f h a.1.1 a.2) :=
  (sourceBaseEnergy_measurable n k f h).comp (measurable_fst.fst.prodMk measurable_snd)

lemma sourceCouplingField_measurable (n k : ℕ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) :
    Measurable (fun a : (SourceBaseData n k × (ℕ → ℝ)) ×
      (NormalizedSpin (n+1) × IndexedLeaf k) =>
      countableGaussianField (sourceGaussianRow p d h u)
        (indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) k) a.1.2 a.2) :=
  measurable_disorder_state_lift (countableGaussianField_measurable
    (sourceGaussianRow_measurable p d h u) (indexedGaussianRowLength_measurable k))

lemma sourceCouplingHamiltonian_measurable (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) :
    Measurable (Function.uncurry (sourceCouplingHamiltonian n k f p d h u)) := by
  exact (sourceCouplingBase_measurable n k f h).add (sourceCouplingField_measurable n k p d h u)

lemma sourceCouplingEnergy_measurable (n k : ℕ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (j : Fin (n+1)) :
    Measurable (Function.uncurry (sourceCouplingEnergy n k p d h j)) :=
  ((countableGaussianField_measurable (sourceGaussianTestRow_measurable p d h j)
    (indexedGaussianRowLength_measurable k)).comp
      (measurable_fst.snd.prodMk measurable_snd)).const_mul _

lemma sourceKernelPressure_shift (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (r : ℝ)
    (a : SourceBaseData n k × (ℕ → ℝ)) :
    sourceKernelPressure n k f p d (u+Pi.single j r) h a =
      (1/(n+1:ℕ))*Real.log (tiltPartition (sourceSpinLeafKernel n k a.1)
        (fun x => sourceCouplingHamiltonian n k f p d h u a x+r*sourceCouplingEnergy n k p d h j a x) 1) := by
  unfold sourceKernelPressure
  congr 3
  funext x
  exact (enrichedIndexedHamiltonian_add_single n _ k f _ p d h u j r a.2 x).trans (by simp only [sourceCouplingHamiltonian,sourceCouplingEnergy,mul_assoc])

lemma sourceCoupling_all_exp_ae (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (z : Fin k → ℝ) (t : ℝ≥0) :
    ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw, ∀ r : ℝ,
      Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x+
        r*sourceCouplingEnergy n k p d h j a x)) (sourceSpinLeafKernel n k a.1) := by
  have he := kernelGaussian_all_coupling_exp_ae (sourceSpinLeafKernel n k) (sourceBaseDataLaw n k z t)
    (sourceBaseEnergy_measurable n k f h) (sourceGaussianRow_measurable p d h u)
    (sourceGaussianTestRow_measurable p d h j) (indexedGaussianRowLength_measurable k)
    (fun a => enrichedIndexedBoundedEnergy_bound n a.1 k f (patternPrefix (n+1) a.1 a.2.1) h)
    (sourceGaussianRow_square_bound p d h u hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l)))
    (sourceGaussianTestRow_square_bound p d h hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l)) j)
  filter_upwards [he] with a ha r
  simpa only [sourceCouplingHamiltonian,enrichedIndexedHamiltonian,sourceBaseEnergy,
    sourceCouplingEnergy,mul_assoc] using ha (r*perturbationAmplitude (n+1) (fun _ => 1) j)

lemma sourceCouplingHamiltonian_section (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (a : SourceBaseData n k × (ℕ → ℝ)) :
    Measurable (sourceCouplingHamiltonian n k f p d h u a) :=
  (sourceCouplingHamiltonian_measurable n k f p d h u).of_uncurry_left

lemma sourceCouplingEnergy_section (n k : ℕ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (j : Fin (n+1)) (a : SourceBaseData n k × (ℕ → ℝ)) :
    Measurable (sourceCouplingEnergy n k p d h j a) :=
  (sourceCouplingEnergy_measurable n k p d h j).of_uncurry_left

lemma sourceCoupling_regular_ae (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (z : Fin k → ℝ) (t : ℝ≥0) :
    ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw,
      let F := fun r => sourceKernelPressure n k f p d (u+Pi.single j r) h a
      let H := sourceCouplingHamiltonian n k f p d h u a
      let Y := sourceCouplingEnergy n k p d h j a
      let μ := sourceSpinLeafKernel n k a.1
      ContDiff ℝ 2 F ∧ ConvexOn ℝ univ F ∧
        (∀ r, HasDerivAt F ((1/(n+1:ℕ))*tiltMean μ (fun x => H x+r*Y x) Y 1) r) ∧
        (∀ r, iteratedDeriv 2 F r = (1/(n+1:ℕ))*tiltMean μ (fun x => H x+r*Y x)
          (fun x => (Y x-tiltMean μ (fun x => H x+r*Y x) Y 1)^2) 1) := by
  filter_upwards [sourceCoupling_all_exp_ae n k f p d h hh0 hh u j z t] with a ha
  dsimp only
  simp_rw [sourceKernelPressure_shift]
  have hH := sourceCouplingHamiltonian_section n k f p d h u a
  have hY := sourceCouplingEnergy_section n k p d h j a
  refine ⟨contDiff_const.mul (coupling_log_contDiff _ hH hY ha),
    (coupling_log_convex _ hH hY ha).smul (by positivity),?_,?_⟩
  · intro r
    exact (coupling_log_hasDerivAt _ hH hY ha r).const_mul _
  · intro r
    rw [iteratedDeriv_const_mul_field]
    congr 1
    exact coupling_log_second_derivative _ hH hY ha r

end SphericalPerceptronFreeEnergy

end

end OAI
