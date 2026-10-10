import Mathlib
import OAI.Probability.Perceptron.Variational.DensityDerivative

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceGaussianField_zero (N k : ℕ) (p d : Fin N→ℕ) (g : ℕ→ℝ)
    (x : NormalizedSpin N×IndexedLeaf k) :
    countableGaussianField (sourceGaussianRow p d (fun _ : Fin (k+1) => 0) (fun _ => 0))
      (indexedGaussianRowLength (I := EnrichedIndex N N p) k) g x=0 := by
  let v := sourceGaussianRow p d (fun _ : Fin (k+1) => 0) (fun _ => 0)
  let L := indexedGaussianRowLength (S := NormalizedSpin N) (I := EnrichedIndex N N p) k
  have hc : countableGaussianCovariance v v L x x=0 := by
    simpa only [v,L,perturbationAmplitude,mul_zero,zero_mul,zero_pow (by omega : 2≠0),
      Finset.sum_const_zero,add_zero] using
      sourceGaussianRow_covariance p d (fun _ : Fin (k+1) => 0) (fun _ => le_rfl)
        monotone_const (fun _ => 0) x x
  have hs : ∑ i : Fin (L x), v i.val x^2=0 := by
    simpa only [countableGaussianCovariance,gaussianPrefixCovariance,
      maskedGaussianCoefficient,Fin.isLt,ite_true,← sq] using hc
  have hv (i : Fin (L x)) : v i.val x=0 := by
    have hi := Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin (L x) => v j.val x^2)
      (fun j _ => sq_nonneg (v j.val x)) (Finset.mem_univ i)
    rw [hs] at hi
    nlinarith [sq_nonneg (v i.val x)]
  change (∑ i : Fin (L x), g i.val*v i.val x)=0
  simp only [hv,mul_zero,Finset.sum_const_zero]

lemma enrichedIndexedHamiltonian_zero (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p d : Fin (n+1)→ℕ) (g : ℕ→ℝ)
    (x : NormalizedSpin (n+1)×IndexedLeaf k) :
    enrichedIndexedHamiltonian n M k f a p d (fun _ => 0) (fun _ => 0) g x=
      normalizedPatternEnergy (n+1) M f a x.1 := by
  simp only [enrichedIndexedHamiltonian,countableGaussianHamiltonian,
    sourceGaussianField_zero,enrichedIndexedBoundedEnergy,mul_zero,sub_zero,add_zero]

def normalizedPatternLog (n M : ℕ) (f : ℝ →ᵇ ℝ) (a : Fin M→Fin (n+1)→ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (normalizedPatternEnergy (n+1) M f a x) ∂unitSphereLaw (n+1))

lemma sourceKernelPressure_zero (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (a : SourceBaseData n k×(ℕ→ℝ)) :
    sourceKernelPressure n k f p d (fun _ => 0) (fun _ => 0) a=
      (1/(n+1:ℕ))*normalizedPatternLog n a.1.1 f (patternPrefix (n+1) a.1.1 a.1.2.1) := by
  simp only [sourceKernelPressure,tiltPartition,sourceSpinLeafKernel_apply,
    enrichedIndexedBaseMeasure,enrichedIndexedHamiltonian_zero,one_mul]
  rw [integral_fun_fst (f := fun x : NormalizedSpin (n+1) => Real.exp
    (normalizedPatternEnergy (n+1) a.1.1 f (patternPrefix (n+1) a.1.1 a.1.2.1) x))]
  simp only [probReal_univ,one_smul,normalizedPatternLog]

lemma normalizedPatternLog_source (α β : ℝ) (φ : ℝ →ᵇ ℝ) (n : ℕ)
    (g : Patterns α (n+1)) :
    (1/(n+1:ℕ))*normalizedPatternLog n (patternCount α (n+1)) (β • φ) g=
      pressure α β φ (n+1) g := by
  unfold pressure sphereLaw
  rw [integral_map (by fun_prop) (by
    apply Continuous.aestronglyMeasurable
    unfold hamiltonian patternField
    fun_prop)]
  simp_rw [← normalizedPatternEnergy_source α β φ n g]
  unfold normalizedPatternLog
  ring

lemma normalizedPatternLog_measurable (n M : ℕ) (f : ℝ →ᵇ ℝ) :
    Measurable (normalizedPatternLog n M f) := by
  have hm := (Real.continuous_exp.comp (normalizedPatternEnergy_continuous (n+1) M f)).measurable
  exact Real.measurable_log.comp hm.stronglyMeasurable.integral_prod_right'.measurable

lemma enrichedExpectedLog_zero (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (z : Fin k→ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (g : Fin M→Fin (n+1)→ℝ) :
    enrichedExpectedLog n M k f p d (fun _ => 0) (fun _ => 0) z g=
      normalizedPatternLog n M f g := by
  have hp := sourceCascadeRealization_preserving n k p z
  have hm := (enrichedCascadeLog_joint_mean n M k f g p d (fun _ => 0) (fun _ => 0)
    z hz hz0 hz1).1.aestronglyMeasurable
  unfold enrichedExpectedLog
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable (by rw [hp.map_eq]; exact hm)]
  have he : ∀ᵐ a ∂((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw),
      enrichedCascadeLog n M k f g p d (fun _ => 0) (fun _ => 0) (sourceCascadeRealization n k p a)=
        normalizedPatternLog n M f g := by
    filter_upwards [(measurePreserving_fst (μ := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)))
      (ν := countableGaussianLaw)).quasiMeasurePreserving.ae
        ((indexedCascadeGood_ae k z hz0 hz1).and (indexedLeafMeasure_regular k z hz hz0 hz1))] with a ha
    rw [show enrichedCascadeLog n M k f g p d (fun _ => 0) (fun _ => 0)
        (sourceCascadeRealization n k p a)=
      Real.log (tiltPartition (enrichedIndexedBaseMeasure n k a.1)
        (enrichedIndexedHamiltonian n M k f g p d (fun _ => 0) (fun _ => 0) a.2) 1) from
          (enrichedIndexedHamiltonian_partition n M k f g p d (fun _ => 0) (fun _ => 0) a.2 a.1 ha.1 ha.2).symm]
    simp only [tiltPartition,enrichedIndexedBaseMeasure,enrichedIndexedHamiltonian_zero,one_mul]
    rw [integral_fun_fst (f := fun x : NormalizedSpin (n+1) => Real.exp (normalizedPatternEnergy (n+1) M f g x))]
    simp only [probReal_univ,one_smul,normalizedPatternLog]
  rw [integral_congr_ae he,integral_const,probReal_univ,one_smul]

lemma sourceCountExpectedLog_zero (n k M : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (z : Fin k→ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    sourceCountExpectedLog n k f p d (fun _ => 0) z (fun _ => 0) M=
      ∫ g, normalizedPatternLog n M f g ∂finitePatternRowsLaw (n+1) M := by
  have hi := (enrichedPoissonLog_section_variance n M k f p d (fun _ => 0) (fun _ => 0)
    z hz hz0 hz1).1.integrable (by norm_num)
  have he : sourceCountExpectedLog n k f p d (fun _ => 0) z (fun _ => 0) M=
      ∫ g, enrichedExpectedLog n M k f p d (fun _ => 0) (fun _ => 0) z (patternPrefix (n+1) M g)
        ∂infinitePatternRowsLaw (n+1) := integral_prod _ hi
  rw [he]
  simp_rw [enrichedExpectedLog_zero n M k f p d z hz hz0 hz1]
  have hp := patternPrefix_measurePreserving (n+1) M
  rw [← integral_map hp.measurable.aemeasurable (normalizedPatternLog_measurable n M f).aestronglyMeasurable,hp.map_eq]

lemma sourceCountExpectedLog_original (α β : ℝ) (φ : ℝ →ᵇ ℝ) (n k : ℕ)
    (p d : Fin (n+1)→ℕ) (z : Fin k→ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    (1/(n+1:ℕ))*sourceCountExpectedLog n k (β • φ) p d (fun _ => 0) z (fun _ => 0)
      (patternCount α (n+1))=expectedPressure α β φ (n+1) := by
  rw [sourceCountExpectedLog_zero n k _ _ p d z hz hz0 hz1,← integral_const_mul]
  simp_rw [normalizedPatternLog_source]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
