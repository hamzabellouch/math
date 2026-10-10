import Mathlib
import OAI.Probability.Perceptron.Variational.LabelRestorationKernel
import OAI.Probability.Perceptron.Variational.LabelRestorationPair

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev SourceLabelPairData (n k : ℕ) :=
  ℕ × ((ℕ→Fin (n+1)→ℝ) × (IndexedCascadeBase k × (((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))))

def sourceLabelPairReassoc (n k : ℕ) :
    ((SourceBaseData n k×(ℕ→ℝ))×((ℕ→ℝ)×(ℕ→ℝ))) ≃ᵐ SourceLabelPairData n k :=
  (MeasurableEquiv.prodAssoc).trans
    (((MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.prodComm)).trans
      ((MeasurableEquiv.prodAssoc).trans
        ((MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.prodAssoc))))

lemma sourceLabelPairReassoc_preserving (n k : ℕ) (z : Fin k→ℝ) (t : ℝ≥0) :
    MeasurePreserving (sourceLabelPairReassoc n k)
      (((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw))
      ((poissonMeasure ((n+1:ℕ)*t)).prod ((infinitePatternRowsLaw (n+1)).prod
        ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
          ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw)))) := by
  let K := poissonMeasure ((n+1:ℕ)*t)
  let R := infinitePatternRowsLaw (n+1)
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  let G := countableGaussianLaw
  exact ((MeasurePreserving.id K).prod (measurePreserving_prodAssoc R B ((G.prod G).prod G))).comp
    ((measurePreserving_prodAssoc K (R.prod B) ((G.prod G).prod G)).comp
      (((MeasurePreserving.id (K.prod (R.prod B))).prod
        (Measure.measurePreserving_swap (μ:=G) (ν:=G.prod G))).comp
        (measurePreserving_prodAssoc (K.prod (R.prod B)) G (G.prod G))))

def labelDepthTest {S : Type} (k : ℕ) (d : Fin (k+1)) (x : Fin 2 → S×IndexedLeaf k) : ℝ :=
  if indexedCommonDepth k (x 0).2 (x 1).2=d then 1 else 0

lemma labelDepthTest_measurable {S : Type} [MeasurableSpace S] (k : ℕ) (d : Fin (k+1)) :
    Measurable (labelDepthTest (S:=S) k d) := by
  have hc : Measurable (fun x : Fin 2 → S×IndexedLeaf k => ((x 0).2,(x 1).2)) :=
    ((measurable_pi_apply 0).snd).prodMk ((measurable_pi_apply 1).snd)
  exact (measurable_of_countable (fun p : IndexedLeaf k×IndexedLeaf k =>
    if indexedCommonDepth k p.1 p.2=d then (1:ℝ) else 0)).comp hc

lemma labelDepthTest_bound {S : Type} (k : ℕ) (d : Fin (k+1)) (x : Fin 2 → S×IndexedLeaf k) :
    |labelDepthTest k d x|≤1 := by unfold labelDepthTest; split <;> norm_num

def sourceLabelPairIntegrand (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ) :=
  labelKernelRestoredRatio (sourceFullSpinLeafKernel n k)
    (sourceCouplingHamiltonian n k f p e h u) q s g.f (fun _ : Fin 2 => v) (fun _ => w) (labelDepthTest k d)

lemma sourceLabelPairIntegrand_integrable (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i,0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ)
    (z : Fin k→ℝ) (t : ℝ≥0) :
    Integrable (sourceLabelPairIntegrand n k f p e h u q g s d v w)
      (((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw)) :=
  labelKernelRestoredRatio_integrable _ _ _ _ _ _ _ _
    (sourceCouplingHamiltonian_measurable n k f p e h u) (labelDepthTest_measurable k d)
    (by norm_num) (labelDepthTest_bound k d) _ (sourceFresh_exp_ae n k f p e h hh0 hh u z t)

lemma sourceLabelPairIntegrand_value (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i,0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1) (t : ℝ≥0) :
    (∫ a, sourceLabelPairIntegrand n k f p e h u q g s d v w a
      ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw)) =
      (twoVisitMass k z d).toReal*(labelPairCoefficient k z q g s v d*labelPairCoefficient k z q g s w d) := by
  let F := sourceLabelPairIntegrand n k f p e h u q g s d v w
  let K := poissonMeasure ((n+1:ℕ)*t)
  let R := infinitePatternRowsLaw (n+1)
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  let G := countableGaussianLaw
  have hi := sourceLabelPairIntegrand_integrable n k f p e h hh0 hh u q g s d v w z t
  have hre := sourceLabelPairReassoc_preserving n k z t
  have hi' := (hre.symm (sourceLabelPairReassoc n k)).integrable_comp_of_integrable hi
  have he := hre.integral_comp (sourceLabelPairReassoc n k).measurableEmbedding
    (fun a => F ((sourceLabelPairReassoc n k).symm a))
  simp only [MeasurableEquiv.symm_apply_apply] at he
  change Integrable (fun a => F ((sourceLabelPairReassoc n k).symm a)) (K.prod (R.prod (B.prod ((G.prod G).prod G)))) at hi'
  change (∫ a, F a ∂_) = _
  rw [he,integral_prod _ hi']
  have ha := hi'.prod_right_ae
  have hval : ∀ᵐ M ∂K, (∫ a, F ((sourceLabelPairReassoc n k).symm (M,a)) ∂(R.prod (B.prod ((G.prod G).prod G)))) =
      (twoVisitMass k z d).toReal*(labelPairCoefficient k z q g s v d*labelPairCoefficient k z q g s w d) := by
    filter_upwards [ha] with M hM
    rw [integral_prod _ hM]
    have hir (a : ℕ→Fin (n+1)→ℝ) :
        (∫ b, F ((sourceLabelPairReassoc n k).symm (M,(a,b))) ∂(B.prod ((G.prod G).prod G))) =
          (twoVisitMass k z d).toReal*(labelPairCoefficient k z q g s v d*labelPairCoefficient k z q g s w d) := by
      refine (integral_congr_ae (ae_of_all _ fun b => ?_)).trans
        (sourceLabelPairRatio_value n M k f (patternPrefix (n+1) M a) p e h hh0 hh u z hz hz0 hz1 q g s d v w)
      change sourceLabelPairIntegrand n k f p e h u q g s d v w (((M,(a,b.1)),b.2.2),b.2.1)=_
      simp only [sourceLabelPairIntegrand,labelKernelRestoredRatio,labelKernelNumerator,labelKernelDenominator,
        sourceFullSpinLeafKernel,Kernel.comap_apply,sourceSpinLeafKernel_apply,sourceCouplingHamiltonian,
        sourceLabelPairRatio]
      rfl
    simp_rw [hir]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  rw [integral_congr_ae hval]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]


lemma labelKernelRestoredRatio_depth {A S : Type} [MeasurableSpace A] [MeasurableSpace S]
    (k : ℕ) (κ : Kernel A (S×IndexedLeaf k)) [IsMarkovKernel κ]
    (H : A → S×IndexedLeaf k → ℝ) (hH : Measurable (Function.uncurry H))
    (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f v w : ℝ →ᵇ ℝ) (c : Fin (k+1)→ℝ)
    (a : A×((ℕ→ℝ)×(ℕ→ℝ))) (hi : Integrable (fun x => Real.exp (H a.1 x)) (κ a.1)) :
    labelKernelRestoredRatio κ H q s f (fun _ : Fin 2 => v) (fun _ => w)
      (fun x => c (indexedCommonDepth k (x 0).2 (x 1).2)) a =
    ∑ d, c d * labelKernelRestoredRatio κ H q s f (fun _ : Fin 2 => v) (fun _ => w)
      (labelDepthTest k d) a := by
  let T (d : Fin (k+1)) : (Fin 2→S×IndexedLeaf k)→ℝ := labelRestorationTest q s f (fun _ : Fin 2 => v) (fun _ => w) (labelDepthTest k d) a.2
  have hT d : Measurable (T d) := labelRestorationTest_measurable q s f _ _ (labelDepthTest_measurable k d) a.2
  let D := (∏ _ : Fin 2, ‖gaussianAverageBCF s (expBCF 1 f*v)‖)*(∏ _ : Fin 2, ‖gaussianAverageBCF s (expBCF 1 f*w)‖)
  have hb d x : |T d x|≤D := by
    simpa only [one_mul] using labelRestorationTest_bound q s f (fun _ : Fin 2 => v) (fun _ => w)
      (by norm_num : (0:ℝ)≤1) (labelDepthTest_bound k d) a.2 x
  have he (x : Fin 2→S×IndexedLeaf k) :
      labelRestorationTest q s f (fun _ : Fin 2 => v) (fun _ => w)
        (fun x => c (indexedCommonDepth k (x 0).2 (x 1).2)) a.2 x = ∑ d, c d*T d x := by
    simp only [T,labelRestorationTest,labelDepthTest]
    simp only [mul_ite,ite_mul,mul_zero,zero_mul]
    simp [mul_assoc]
  let := tilt_law_probability_of_integrable (κ a.1) (by simpa only [one_mul] using hi :
    Integrable (fun x => Real.exp (1*H a.1 x)) (κ a.1))
  have hiT d : Integrable (T d) (Measure.pi fun _ : Fin 2 => tiltLaw (κ a.1) (H a.1) 1) :=
    Integrable.of_bound (hT d).aestronglyMeasurable D (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb d x)
  simp only [labelKernelRestoredRatio,labelKernelNumerator,gibbsReplicaMean_integral_of_integrable _ hH.of_uncurry_left hi]
  simp_rw [he]
  rw [integral_finsetSum _ (fun d _ => (hiT d).const_mul (c d)),Finset.sum_div]
  simp only [integral_const_mul]
  apply Finset.sum_congr rfl
  intro d _
  dsimp only [T]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
