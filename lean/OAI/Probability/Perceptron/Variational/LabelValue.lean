import Mathlib
import OAI.Probability.Perceptron.Variational.LeafGibbsMarginal
import OAI.Probability.Perceptron.Variational.LabelReferenceValue
import OAI.Probability.Perceptron.Cavity.LabelFreshLog

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev SourceLabelData (n k : ℕ) :=
  ℕ × ((ℕ→Fin (n+1)→ℝ) × (IndexedCascadeBase k × ((ℕ→ℝ)×(ℕ→ℝ))))

def sourceLabelReassoc (n k : ℕ) :
    ((SourceBaseData n k × (ℕ→ℝ)) × (ℕ→ℝ)) ≃ᵐ SourceLabelData n k :=
  (MeasurableEquiv.prodAssoc).trans
    (((MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.prodComm)).trans
      ((MeasurableEquiv.prodAssoc).trans
        ((MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.prodAssoc))))

lemma sourceLabelReassoc_preserving (n k : ℕ) (z : Fin k→ℝ) (t : ℝ≥0) :
    MeasurePreserving (sourceLabelReassoc n k)
      (((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod countableGaussianLaw)
      ((poissonMeasure ((n+1:ℕ)*t)).prod ((infinitePatternRowsLaw (n+1)).prod
        ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
          (countableGaussianLaw.prod countableGaussianLaw)))) := by
  let K := poissonMeasure ((n+1:ℕ)*t)
  let R := infinitePatternRowsLaw (n+1)
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  let G := countableGaussianLaw
  exact ((MeasurePreserving.id K).prod (measurePreserving_prodAssoc R B (G.prod G))).comp
    ((measurePreserving_prodAssoc K (R.prod B) (G.prod G)).comp
      (((MeasurePreserving.id (K.prod (R.prod B))).prod (Measure.measurePreserving_swap (μ := G) (ν := G))).comp
        (measurePreserving_prodAssoc (K.prod (R.prod B)) G G)))

def sourceLabelLogIntegrand (n k : ℕ) (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ)
    (u : Fin (n+1)→ℝ) (a : (SourceBaseData n k × (ℕ→ℝ)) × (ℕ→ℝ)) : ℝ :=
  Real.log (boundedThermalPartition (sourceFullSpinLeafKernel n k)
    (sourceCouplingHamiltonian n k f p d h u) (labelLogResponse q hq1 ψ) a)

lemma sourceLabelLogIntegrand_measurable (n k : ℕ) (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) :
    Measurable (sourceLabelLogIntegrand n k q hq1 f ψ p d h u) :=
  (boundedThermalPartition_measurable _ _ (sourceCouplingHamiltonian_measurable n k f p d h u)
    _ (labelLogResponse_measurable q hq1 ψ)).log

lemma sourceLabelLogIntegrand_bound (n k : ℕ) (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (a : (SourceBaseData n k × (ℕ→ℝ)) × (ℕ→ℝ)) :
    |sourceLabelLogIntegrand n k q hq1 f ψ p d h u a|≤‖ψ‖ :=
  boundedThermalPartition_log_bound _ _ (sourceCouplingHamiltonian_measurable n k f p d h u)
    _ (labelLogResponse_measurable q hq1 ψ) ψ (labelLogResponse_bound q hq1 ψ) a

lemma sourceLabelLogIntegrand_integrable {D : Type*} [MeasurableSpace D]
    (n k : ℕ) (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (μ : Measure D) [IsFiniteMeasure μ]
    (e : D→(SourceBaseData n k × (ℕ→ℝ)) × (ℕ→ℝ)) (he : Measurable e) :
    Integrable (fun a => sourceLabelLogIntegrand n k q hq1 f ψ p d h u (e a)) μ := by
  apply Integrable.of_bound
    ((sourceLabelLogIntegrand_measurable n k q hq1 f ψ p d h u).comp he).aestronglyMeasurable ‖ψ‖
  exact ae_of_all _ fun a => by
    change |sourceLabelLogIntegrand n k q hq1 f ψ p d h u (e a)|≤‖ψ‖
    exact sourceLabelLogIntegrand_bound n k q hq1 f ψ p d h u (e a)

lemma enrichedIndexedHamiltonian_exp_ae (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (b : IndexedCascadeBase k) :
    ∀ᵐ g ∂countableGaussianLaw, Integrable
      (fun x => Real.exp (enrichedIndexedHamiltonian n M k f a p d h u g x))
      (enrichedIndexedBaseMeasure n k b) := by
  have he := countableGaussian_coupling_exp_ae (enrichedIndexedBaseMeasure n k b)
    (enrichedIndexedBoundedEnergy_measurable n M k f a h)
    (sourceGaussianRow_measurable p d h u) (sourceGaussianRow_measurable p d h u)
    (indexedGaussianRowLength_measurable k)
    (enrichedIndexedBoundedEnergy_bound n M k f a h)
    (sourceGaussianRow_square_bound p d h u hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l)))
    (sourceGaussianRow_square_bound p d h u hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l))) 0
  simpa only [zero_mul,add_zero,enrichedIndexedHamiltonian] using he

def labelProfileValue (k : ℕ) (z : Fin k→ℝ) (q : Fin (k+1)→ℝ)
    (hq1 : q (Fin.last k)≤1) (g : Jet3) : ℝ :=
  ∫ x, gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ (Fin 1)))
    (linearCascadeWord (fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => q l) j)) k z)
    (labelProfileTerminal g ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩)
    (diagonalMark (profileGaussianRoot (fun l (_ : Fin 1) => q l)) x)
    ∂stdGaussian (EuclideanSpace ℝ (Fin 1))

lemma sourceLabelLogIntegrand_fixed_value (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : ℕ→Fin (n+1)→ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1) (g : Jet3) :
    (∫ t : IndexedCascadeBase k×((ℕ→ℝ)×(ℕ→ℝ)),
      sourceLabelLogIntegrand n k q hq1 f g.f p d h u (((M,(a,t.1)),t.2.2),t.2.1)
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        (countableGaussianLaw.prod countableGaussianLaw))=labelProfileValue k z q hq1 g := by
  let e : IndexedCascadeBase k×((ℕ→ℝ)×(ℕ→ℝ))→SourceBaseData n k×(ℕ→ℝ) :=
    fun t => ((M,(a,t.1)),t.2.2)
  have he : Measurable e := by unfold e; fun_prop
  let κ := (sourceFullSpinLeafKernel n k).comap e he
  let H := fun t x => sourceCouplingHamiltonian n k f p d h u (e t) x
  have hH : Measurable (Function.uncurry H) :=
    (sourceCouplingHamiltonian_measurable n k f p d h u).comp
      ((he.comp measurable_fst).prodMk measurable_snd)
  have hm : MeasurableSet {t | Integrable (fun x => Real.exp (H t x)) (κ t)} :=
    measurableSet_kernel_integrable (κ := κ) (f := fun t x => Real.exp (H t x))
      hH.exp.stronglyMeasurable
  have hi : ∀ᵐ t ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
      (countableGaussianLaw.prod countableGaussianLaw),
      Integrable (fun x => Real.exp (H t x)) (κ t) := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    refine ae_of_all _ fun b => ?_
    have ht := (measurePreserving_snd (μ := countableGaussianLaw) (ν := countableGaussianLaw)).quasiMeasurePreserving.ae
      (enrichedIndexedHamiltonian_exp_ae n M k f (patternPrefix (n+1) M a) p d h hh0 hh u b)
    simpa only [κ,Kernel.comap_apply,H,e,sourceFullSpinLeafKernel,sourceSpinLeafKernel_apply,
      sourceCouplingHamiltonian] using ht
  refine (integral_congr_ae ?_).trans
    (source_countable_label_reference_value n M k f (patternPrefix (n+1) M a) p d h u
      z hz hz0 hz1 q hq1 g)
  filter_upwards [hi] with t ht
  have ht' : Integrable
      (fun x => Real.exp (enrichedIndexedHamiltonian n M k f (patternPrefix (n+1) M a) p d h u t.2.2 x))
      (enrichedIndexedBaseMeasure n k t.1) := by
    simpa only [κ,Kernel.comap_apply,H,e,sourceFullSpinLeafKernel,sourceSpinLeafKernel_apply,
      sourceCouplingHamiltonian] using ht
  unfold sourceLabelLogIntegrand boundedThermalPartition
  simp only [labelLogResponse_exp,sourceFullSpinLeafKernel,Kernel.comap_apply,
    sourceSpinLeafKernel_apply,sourceCouplingHamiltonian]
  congr 1
  exact enrichedIndexedHamiltonian_leaf_observable n M k f (patternPrefix (n+1) M a) p d h u
    t.2.2 t.1 ht' (fun l => gaussianAverageBCF
      ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩ (expBCF 1 g.f) (labelProfileField q t.2.1 ((),l)))
    (fun l => (gaussianAverageBCF _ (expBCF 1 g.f)).norm_coe_le_norm _)

theorem sourceLabelFreshLog_value (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1) (g : Jet3) (t : ℝ≥0) :
    sourceLabelFreshLog n k q hq1 f g.f p d h u z t=labelProfileValue k z q hq1 g := by
  let F := sourceLabelLogIntegrand n k q hq1 f g.f p d h u
  let K := poissonMeasure ((n+1:ℕ)*t)
  let R := infinitePatternRowsLaw (n+1)
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  let G := countableGaussianLaw
  have hi := sourceLabelLogIntegrand_integrable n k q hq1 f g.f p d h u
    (((sourceBaseDataLaw n k z t).prod G).prod G) id measurable_id
  change Integrable F (((sourceBaseDataLaw n k z t).prod G).prod G) at hi
  have he : sourceLabelFreshLog n k q hq1 f g.f p d h u z t=
      ∫ a, F a ∂((sourceBaseDataLaw n k z t).prod G).prod G := by
    rw [integral_prod _ hi]
    simp only [F,sourceLabelLogIntegrand,boundedThermalPartition,labelLogResponse_exp,sourceLabelFreshLog,G]
  rw [he]
  have hp := (sourceLabelReassoc_preserving n k z t).integral_comp
    (sourceLabelReassoc n k).measurableEmbedding (fun a => F ((sourceLabelReassoc n k).symm a))
  simp only [MeasurableEquiv.symm_apply_apply] at hp
  rw [hp]
  have hi' := sourceLabelLogIntegrand_integrable n k q hq1 f g.f p d h u
    (K.prod (R.prod (B.prod (G.prod G)))) (sourceLabelReassoc n k).symm
    (sourceLabelReassoc n k).symm.measurable
  change Integrable (fun a => F ((sourceLabelReassoc n k).symm a))
    (K.prod (R.prod (B.prod (G.prod G)))) at hi'
  rw [integral_prod _ hi']
  have hv (M : ℕ) : (∫ a, F ((sourceLabelReassoc n k).symm (M,a))
      ∂(R.prod (B.prod (G.prod G))))=labelProfileValue k z q hq1 g := by
    have hiM := sourceLabelLogIntegrand_integrable n k q hq1 f g.f p d h u
      (R.prod (B.prod (G.prod G))) (fun a => (sourceLabelReassoc n k).symm (M,a))
      ((sourceLabelReassoc n k).symm.measurable.comp (measurable_const.prodMk measurable_id))
    change Integrable (fun a => F ((sourceLabelReassoc n k).symm (M,a)))
      (R.prod (B.prod (G.prod G))) at hiM
    rw [integral_prod _ hiM]
    have hval (a : ℕ→Fin (n+1)→ℝ) :
        (∫ b, F ((sourceLabelReassoc n k).symm (M,(a,b))) ∂(B.prod (G.prod G)))=
          labelProfileValue k z q hq1 g :=
      sourceLabelLogIntegrand_fixed_value n M k f a p d h hh0 hh u z hz hz0 hz1 q hq1 g
    simp_rw [hval]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  simp_rw [hv]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

end SphericalPerceptronFreeEnergy
end

end OAI
