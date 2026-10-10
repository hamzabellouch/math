import Mathlib
import OAI.Probability.Perceptron.Cavity.FreshMomentLimit
import OAI.Probability.Perceptron.Variational.FixedCount

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceDisorderUnassoc (n k : ℕ) (a : SourceIndexedDisorder n k) : SourceBaseData n k × (ℕ→ℝ) :=
  ((a.1,(a.2.1,a.2.2.1)),a.2.2.2)

lemma sourceDisorderUnassoc_preserving (n k : ℕ) (z : Fin k→ℝ) (t : ℝ≥0) :
    MeasurePreserving (sourceDisorderUnassoc n k) (sourceIndexedDisorderLaw n k z t)
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) := by
  let K := poissonMeasure ((n+1:ℕ)*t)
  let R := infinitePatternRowsLaw (n+1)
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  exact (measurePreserving_prodAssoc K (R.prod B) countableGaussianLaw).symm.comp
    ((MeasurePreserving.id K).prod (measurePreserving_prodAssoc R B countableGaussianLaw).symm)

theorem sourceDensityIncrement_eq_fresh (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    sourceDensityIncrement n k f p d h z u t=sourceFreshLog n k f p d h u z t := by
  let J := fun a : SourceBaseData n k × (ℕ→ℝ) =>
    ∫ g, Real.log (freshThermalPartition (sourceFullSpinLeafKernel n k)
      (sourceCouplingHamiltonian n k f p d h u) (fun x => x.1.val) f (a,g))
      ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)))
  have hi := freshThermalPartition_log_integrable (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (sourceCouplingHamiltonian n k f p d h u) (sourceCouplingHamiltonian_measurable n k f p d h u)
    (fun x => x.1.val) (measurable_subtype_coe.comp measurable_fst) f
    (sourceFresh_exp_ae n k f p d h hh0 hh u z t)
  have hj : Integrable J ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) :=
    hi.integral_prod_left
  have hp := sourceDisorderUnassoc_preserving n k z t
  have he (M : ℕ) (a : SourceCountData n k) : J (sourceDisorderUnassoc n k (M,a))=
      ∫ g, Real.log (freshThermalPartition (sourceCountKernel n k)
        (sourceCountHamiltonian n M k f p d h u) (fun x => x.1.val) f (a,g))
          ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1))) := by
    apply integral_congr_ae
    exact ae_of_all _ fun g => by
      simp only [freshThermalPartition,sourceFullSpinLeafKernel,Kernel.comap_apply,
        sourceSpinLeafKernel_apply,sourceCountKernel_apply]
      rfl
  rw [sourceDensityIncrement]
  simp_rw [sourceCountExpectedLog_fresh n _ k f p d h hh0 hh u z hz hz0 hz1,← he]
  change (∫ M, ∫ a, J (sourceDisorderUnassoc n k (M,a)) ∂sourceCountLaw n k z
    ∂poissonMeasure ((n+1:ℕ)*t))=_
  calc
    _=(∫ a, J (sourceDisorderUnassoc n k a) ∂sourceIndexedDisorderLaw n k z t) := by
      simpa only [Function.comp_def,sourceCountLaw,sourceIndexedDisorderLaw] using
        (integral_prod _ (hp.integrable_comp_of_integrable hj)).symm
    _=sourceFreshLog n k f p d h u z t := ?_
  have hmap := integral_map (φ := sourceDisorderUnassoc n k) (f := J) hp.measurable.aemeasurable
    (by rw [hp.map_eq]; exact hj.aestronglyMeasurable)
  rw [hp.map_eq] at hmap
  exact hmap.symm

end SphericalPerceptronFreeEnergy
end

end OAI
