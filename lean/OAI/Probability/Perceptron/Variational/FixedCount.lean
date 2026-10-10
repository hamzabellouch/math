import Mathlib
import OAI.Probability.Perceptron.Cavity.FreshThermalLaw
import OAI.Probability.Perceptron.Variational.DensityDerivative
import OAI.Probability.Perceptron.Cavity.FreshLogRatio

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev SourceCountData (n k : ℕ) := (ℕ→Fin (n+1)→ℝ) × (IndexedCascadeBase k × (ℕ→ℝ))

def sourceCountLaw (n k : ℕ) (z : Fin k→ℝ) : Measure (SourceCountData n k) :=
  (infinitePatternRowsLaw (n+1)).prod
    ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)
instance (n k : ℕ) (z : Fin k→ℝ) : IsProbabilityMeasure (sourceCountLaw n k z) := by
  unfold sourceCountLaw
  infer_instance

def sourceCountEmbedding (n M k : ℕ) (a : SourceCountData n k) : SourceBaseData n k × (ℕ→ℝ) :=
  ((M,(a.1,a.2.1)),a.2.2)

lemma sourceCountEmbedding_measurable (n M k : ℕ) : Measurable (sourceCountEmbedding n M k) := by
  unfold sourceCountEmbedding
  fun_prop

def sourceCountKernel (n k : ℕ) : Kernel (SourceCountData n k) (NormalizedSpin (n+1) × IndexedLeaf k) :=
  (sourceFullSpinLeafKernel n k).comap (sourceCountEmbedding n 0 k) (sourceCountEmbedding_measurable n 0 k)
instance (n k : ℕ) : IsMarkovKernel (sourceCountKernel n k) := by
  unfold sourceCountKernel
  infer_instance

lemma sourceCountKernel_apply (n k : ℕ) (a : SourceCountData n k) :
    sourceCountKernel n k a=enrichedIndexedBaseMeasure n k a.2.1 := by
  simp only [sourceCountKernel,Kernel.comap_apply,sourceFullSpinLeafKernel,sourceCountEmbedding,
    sourceSpinLeafKernel_apply]

def sourceCountHamiltonian (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (a : SourceCountData n k) : NormalizedSpin (n+1) × IndexedLeaf k → ℝ :=
  sourceCouplingHamiltonian n k f p d h u (sourceCountEmbedding n M k a)

lemma sourceCountHamiltonian_measurable (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) :
    Measurable (Function.uncurry (sourceCountHamiltonian n M k f p d h u)) := by
  have hm : Measurable (fun a : SourceCountData n k × (NormalizedSpin (n+1) × IndexedLeaf k) =>
      (sourceCountEmbedding n M k a.1,a.2)) :=
    ((sourceCountEmbedding_measurable n M k).comp measurable_fst).prodMk measurable_snd
  have he : Function.uncurry (sourceCountHamiltonian n M k f p d h u) =
      (Function.uncurry (sourceCouplingHamiltonian n k f p d h u)) ∘
        (fun a : SourceCountData n k × (NormalizedSpin (n+1) × IndexedLeaf k) =>
          (sourceCountEmbedding n M k a.1,a.2)) := rfl
  rw [he]
  exact Measurable.comp (sourceCouplingHamiltonian_measurable n k f p d h u) hm

def sourceCountLog (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (a : SourceCountData n k) : ℝ :=
  Real.log (tiltPartition (sourceCountKernel n k a) (sourceCountHamiltonian n M k f p d h u a) 1)

lemma sourceCountLog_ae (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    sourceCountLog n M k f p d h u =ᵐ[sourceCountLaw n k z]
      fun a => enrichedPoissonLog n k f p d u h (M,(a.1,sourceCascadeRealization n k p a.2)) := by
  have hp : MeasurePreserving (fun a : SourceCountData n k => a.2.1)
      (sourceCountLaw n k z) (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) :=
    measurePreserving_fst.comp measurePreserving_snd
  filter_upwards [hp.quasiMeasurePreserving.ae ((indexedCascadeGood_ae k z hz0 hz1).and
    (indexedLeafMeasure_regular k z hz hz0 hz1))] with a ha
  rw [sourceCountLog,sourceCountKernel_apply]
  exact enrichedIndexedHamiltonian_partition n M k f _ p d h u a.2.2 a.2.1 ha.1 ha.2

lemma sourceCountLog_memLp (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    MemLp (sourceCountLog n M k f p d h u) 2 (sourceCountLaw n k z) := by
  have hp : MeasurePreserving (Prod.map id (sourceCascadeRealization n k p)) (sourceCountLaw n k z)
      (enrichedRowsDisorderLaw n k p z) :=
    (MeasurePreserving.id (infinitePatternRowsLaw (n+1))).prod
      (sourceCascadeRealization_preserving n k p z)
  exact ((enrichedPoissonLog_section_variance n M k f p d u h z hz hz0 hz1).1.comp_measurePreserving hp).ae_eq
    (sourceCountLog_ae n M k f p d h u z hz hz0 hz1).symm

lemma sourceCountExpectedLog_eq (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    sourceCountExpectedLog n k f p d h z u M=
      ∫ a, sourceCountLog n M k f p d h u a ∂sourceCountLaw n k z := by
  rw [integral_congr_ae (sourceCountLog_ae n M k f p d h u z hz hz0 hz1)]
  have hp : MeasurePreserving (Prod.map id (sourceCascadeRealization n k p)) (sourceCountLaw n k z)
      (enrichedRowsDisorderLaw n k p z) :=
    (MeasurePreserving.id (infinitePatternRowsLaw (n+1))).prod
      (sourceCascadeRealization_preserving n k p z)
  have hi := (enrichedPoissonLog_section_variance n M k f p d u h z hz hz0 hz1).1
  unfold sourceCountExpectedLog
  rw [← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable (by rw [hp.map_eq]; exact hi.aestronglyMeasurable))

lemma sourceCount_exp_ae (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) :
    ∀ᵐ a ∂sourceCountLaw n k z,
      Integrable (fun x => Real.exp (sourceCountHamiltonian n M k f p d h u a x))
        (sourceCountKernel n k a) := by
  have hm : MeasurableSet {a : SourceCountData n k | Integrable
      (fun x => Real.exp (sourceCountHamiltonian n M k f p d h u a x)) (sourceCountKernel n k a)} :=
    measurableSet_kernel_integrable (κ := sourceCountKernel n k)
      (f := fun a x => Real.exp (sourceCountHamiltonian n M k f p d h u a x))
      (sourceCountHamiltonian_measurable n M k f p d h u).exp.stronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  refine ae_of_all _ fun a => ?_
  have hm' : MeasurableSet {b : IndexedCascadeBase k × (ℕ→ℝ) |
      Integrable (fun x => Real.exp (sourceCountHamiltonian n M k f p d h u (a,b) x))
        (sourceCountKernel n k (a,b))} := hm.preimage (measurable_const.prodMk measurable_id)
  apply (Measure.ae_prod_iff_ae_ae hm').mpr
  refine ae_of_all _ fun b => ?_
  have he := countableGaussian_coupling_exp_ae (enrichedIndexedBaseMeasure n k b)
    (enrichedIndexedBoundedEnergy_measurable n M k f (patternPrefix (n+1) M a) h)
    (sourceGaussianRow_measurable p d h u) (sourceGaussianRow_measurable p d h u)
    (indexedGaussianRowLength_measurable k)
    (enrichedIndexedBoundedEnergy_bound n M k f (patternPrefix (n+1) M a) h)
    (sourceGaussianRow_square_bound p d h u hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l)))
    (sourceGaussianRow_square_bound p d h u hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l))) 0
  simpa only [zero_mul,add_zero,sourceCountHamiltonian,sourceCountKernel_apply,
    sourceCountEmbedding,sourceCouplingHamiltonian,enrichedIndexedHamiltonian] using he

lemma sourceCountHamiltonian_succ (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (a : SourceCountData n k)
    (x : NormalizedSpin (n+1) × IndexedLeaf k) :
    sourceCountHamiltonian n (M+1) k f p d h u a x=
      sourceCountHamiltonian n M k f p d h u a x+f (inner ℝ x.1.val (WithLp.toLp 2 (a.1 M))) := by
  simp only [sourceCountHamiltonian,sourceCountEmbedding,sourceCouplingHamiltonian,
    enrichedIndexedHamiltonian,countableGaussianHamiltonian,enrichedIndexedBoundedEnergy]
  rw [normalizedPatternEnergy_prefix_exact]
  ring

lemma sourceCountLog_succ (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) :
    ∀ᵐ a ∂sourceCountLaw n k z,
      sourceCountLog n (M+1) k f p d h u a-sourceCountLog n M k f p d h u a=
      Real.log (freshThermalPartition (sourceCountKernel n k)
        (sourceCountHamiltonian n M k f p d h u) (fun x => x.1.val) f
        (a,WithLp.toLp 2 (a.1 M))) := by
  filter_upwards [sourceCount_exp_ae n M k f p d h hh0 hh u z] with a ha
  unfold sourceCountLog
  have hH := funext (sourceCountHamiltonian_succ n M k f p d h u a)
  rw [hH]
  exact tilt_log_add_bounded _ _ _
    (sourceCountHamiltonian_measurable n M k f p d h u).of_uncurry_left
    (f.measurable.comp ((measurable_subtype_coe.comp measurable_fst).inner measurable_const))
    (fun x => f.norm_coe_le_norm _) ha

lemma sourceCountFreshLog_prefix (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (a : SourceCountData n k)
    (g : EuclideanSpace ℝ (Fin (n+1))) :
    freshThermalPartition (sourceCountKernel n k) (sourceCountHamiltonian n M k f p d h u)
      (fun x => x.1.val) f ((patternExtend (n+1) M (patternPrefix (n+1) M a.1),a.2),g)=
    freshThermalPartition (sourceCountKernel n k) (sourceCountHamiltonian n M k f p d h u)
      (fun x => x.1.val) f (a,g) := by
  unfold freshThermalPartition
  simp only [sourceCountKernel_apply,sourceCountHamiltonian,sourceCountEmbedding,
    sourceCouplingHamiltonian,patternPrefix_extend]

lemma sourceCountExpectedLog_fresh (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    sourceCountExpectedLog n k f p d h z u (M+1)-sourceCountExpectedLog n k f p d h z u M=
      ∫ a, ∫ g, Real.log (freshThermalPartition (sourceCountKernel n k)
        (sourceCountHamiltonian n M k f p d h u) (fun x => x.1.val) f (a,g))
        ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1))) ∂sourceCountLaw n k z := by
  let FT := freshThermalPartition (sourceCountKernel n k)
    (sourceCountHamiltonian n M k f p d h u) (fun x => x.1.val) f
  have hm : Measurable FT := freshThermalPartition_measurable (sourceCountKernel n k)
    (sourceCountHamiltonian n M k f p d h u) (sourceCountHamiltonian_measurable n M k f p d h u)
    (fun x => x.1.val) (measurable_subtype_coe.comp measurable_fst) f
  let F : ((Fin M→Fin (n+1)→ℝ) × EuclideanSpace ℝ (Fin (n+1))) ×
      (IndexedCascadeBase k × (ℕ→ℝ)) → ℝ :=
    fun a => Real.log (FT ((patternExtend (n+1) M a.1.1,a.2),a.1.2))
  have hF : Measurable F := hm.log.comp
    ((((patternExtend_measurable (n+1) M).comp measurable_fst.fst).prodMk measurable_snd).prodMk measurable_fst.snd)
  have he a g : F ((patternPrefix (n+1) M a.1,g),a.2)=Real.log (FT (a,g)) :=
    congrArg Real.log (sourceCountFreshLog_prefix n M k f p d h u a g)
  have hi1 := (sourceCountLog_memLp n (M+1) k f p d h u z hz hz0 hz1).integrable (by norm_num)
  have hi0 := (sourceCountLog_memLp n M k f p d h u z hz hz0 hz1).integrable (by norm_num)
  have hi : Integrable (fun a => Real.log (FT (a,WithLp.toLp 2 (a.1 M)))) (sourceCountLaw n k z) :=
    (hi1.sub hi0).congr (sourceCountLog_succ n M k f p d h hh0 hh u z)
  rw [sourceCountExpectedLog_eq n (M+1) k f p d h u z hz hz0 hz1,
    sourceCountExpectedLog_eq n M k f p d h u z hz hz0 hz1,← integral_sub hi1 hi0,
    integral_congr_ae (sourceCountLog_succ n M k f p d h hh0 hh u z)]
  have hind := patternPrefix_fresh_product_integral
    ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)
    (n+1) M F hF (hi.congr (ae_of_all _ fun a => (he a _).symm))
  simpa only [he,FT,sourceCountLaw] using hind

end SphericalPerceptronFreeEnergy
end

end OAI
