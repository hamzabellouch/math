import Mathlib
import OAI.Probability.Perceptron.Variational.LabelRestorationSingle

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators BoundedContinuousFunction Topology

def sourceLabelSingleIntegrand (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ) :=
  labelKernelRestoredRatio (sourceFullSpinLeafKernel n k)
    (sourceCouplingHamiltonian n k f p e h u) q s g.f (fun _ : Fin 1 => v) (fun _ => w) (fun _ => 1)

lemma sourceLabelSingleIntegrand_integrable (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i,0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ)
    (z : Fin k→ℝ) (t : ℝ≥0) :
    Integrable (sourceLabelSingleIntegrand n k f p e h u q g s v w)
      (((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw)) :=
  labelKernelRestoredRatio_integrable _ _ _ _ _ _ _ _
    (sourceCouplingHamiltonian_measurable n k f p e h u) measurable_const
    (show (0:ℝ)≤1 by norm_num) (fun _ => by norm_num) _ (sourceFresh_exp_ae n k f p e h hh0 hh u z t)

lemma sourceLabelSingleIntegrand_value (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i,0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1) (t : ℝ≥0) :
    (∫ a, sourceLabelSingleIntegrand n k f p e h u q g s v w a
      ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw)) =
      labelSingleCoefficient k z q g s v*labelSingleCoefficient k z q g s w := by
  let F := sourceLabelSingleIntegrand n k f p e h u q g s v w
  let K := poissonMeasure ((n+1:ℕ)*t)
  let R := infinitePatternRowsLaw (n+1)
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  let G := countableGaussianLaw
  have hi := sourceLabelSingleIntegrand_integrable n k f p e h hh0 hh u q g s v w z t
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
      labelSingleCoefficient k z q g s v*labelSingleCoefficient k z q g s w := by
    filter_upwards [ha] with M hM
    rw [integral_prod _ hM]
    have hir (a : ℕ→Fin (n+1)→ℝ) :
        (∫ b, F ((sourceLabelPairReassoc n k).symm (M,(a,b))) ∂(B.prod ((G.prod G).prod G))) =
          labelSingleCoefficient k z q g s v*labelSingleCoefficient k z q g s w := by
      refine (integral_congr_ae (ae_of_all _ fun b => ?_)).trans
        (sourceLabelSingleRatio_value n M k f (patternPrefix (n+1) M a) p e h hh0 hh u z hz hz0 hz1 q g s v w)
      change sourceLabelSingleIntegrand n k f p e h u q g s v w (((M,(a,b.1)),b.2.2),b.2.1)=_
      simp only [sourceLabelSingleIntegrand,labelKernelRestoredRatio,labelKernelNumerator,labelKernelDenominator,
        sourceFullSpinLeafKernel,Kernel.comap_apply,sourceSpinLeafKernel_apply,sourceCouplingHamiltonian,
        sourceLabelSingleRatio]
    simp_rw [hir]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  rw [integral_congr_ae hval]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

def singleRestorationBound (f v w : ℝ →ᵇ ℝ) : ℝ :=
  ‖expBCF 1 f*v‖*‖expBCF 1 f*w‖

lemma singleRestorationBound_nonneg (f v w : ℝ →ᵇ ℝ) : 0≤ singleRestorationBound f v w := by
  unfold singleRestorationBound; positivity

lemma sourceLabelRestorationNumerator_single_bound (n k : ℕ) (f ψ v w : ℝ →ᵇ ℝ)
    (q : Fin (k+1)→Time) (s : ℝ≥0)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (a) :
    |sourceLabelRestorationNumerator n k 1 (fun i => (q i:ℝ)) s f ψ
      (fun _ => v) (fun _ => w) 1 p e h u a|≤ singleRestorationBound ψ v w := by
  let : Nonempty (CompactBlock CompactJointOverlap 1) :=
    ⟨fun _ _ => (⟨0,by norm_num,by norm_num⟩,⟨0,by norm_num,by norm_num⟩)⟩
  simpa [singleRestorationBound] using sourceLabelRestorationNumerator_bound n k 1
    (fun i => (q i:ℝ)) s f ψ (fun _ => v) (fun _ => w) 1 p e h u a

lemma sourceLabelRestorationRatio_single_value (n k : ℕ) (f : ℝ →ᵇ ℝ) (g : Jet3)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i,0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (q : Fin (k+1)→Time) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1) (t : ℝ≥0) :
    sourceLabelRestorationRatio n k 1 (fun i => (q i:ℝ)) s f g.f (fun _ => v) (fun _ => w)
      1 p e h u z t =
      labelSingleCoefficient k z (fun i => (q i:ℝ)) g s v *
        labelSingleCoefficient k z (fun i => (q i:ℝ)) g s w := by
  rw [sourceLabelRestorationRatio_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh0 hh]
  exact sourceLabelSingleIntegrand_value n k f p e h hh0 hh u _ g s v w z hz hz0 hz1 t

lemma sourceLabelSingle_witness (k : ℕ) (q : Fin (k+1)→Time) (hq : Monotone q)
    (f : ℝ →ᵇ ℝ) (g : Jet3) (v w : ℝ →ᵇ ℝ)
    (p e : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (hh0 : ∀ n i,0≤h n i) (hh : ∀ n,Monotone (h n)) (u : (n : ℕ)→Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (t : ℕ→ℝ≥0) (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (e (s n)) (h (s n))
      (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∃ η : ProbabilityMeasure (WeightedRestorationRange g.f (singleRestorationBound g.f v w)),
      (∀ j, (∫ x, x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v w))))=
        ∫ Q, labelRestorationBlockMoment (fun i => (q i:ℝ)) g.f (fun _ : Fin 1 => v) (fun _ => w)
          1 j (compactBlock (1+j) Q) ∂ν) ∧
      (∫ x, x.1.val*restorationReciprocal g.f 1 x.2 ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v w))))=
        labelSingleCoefficient k z (fun i => (q i:ℝ)) g (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) v *
        labelSingleCoefficient k z (fun i => (q i:ℝ)) g (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) w := by
  let τ : ℝ≥0 := ⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩
  apply compactWeighted_witness
    (fun n => ((sourceBaseDataLaw (s n) k z (t (s n))).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw))
    g.f (singleRestorationBound g.f v w)
    (fun n => sourceLabelRestorationNumerator (s n) k 1 (fun i => (q i:ℝ)) τ f g.f (fun _ => v) (fun _ => w)
      1 (p (s n)) (e (s n)) (h (s n)) (u (s n)))
    (fun n => sourceLabelRestorationDenominator (s n) k (fun i => (q i:ℝ)) τ f g.f
      (p (s n)) (e (s n)) (h (s n)) (u (s n)))
    (fun n => sourceLabelRestorationNumerator_measurable ..)
    (fun n => sourceLabelRestorationDenominator_measurable ..)
    (fun n a => sourceLabelRestorationNumerator_single_bound ..) _ ?_ (restorationReciprocal g.f 1) _ ?_
  · intro j
    simp_rw [sourceLabelRestorationPolynomial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hh0 _) (hh _) j]
    exact sourceLabelRestorationMoment_tendsto k 1 (fun i => (q i:ℝ)) (q 0).prop.1
      (fun i l hil => hq hil) (q (Fin.last k)).prop.2 f g.f (fun _ => v) (fun _ => w)
      1 p e h hh0 hh u z t s hlim j
  · change Tendsto (fun n => sourceLabelRestorationRatio (s n) k 1 (fun i => (q i:ℝ)) τ f g.f
      (fun _ => v) (fun _ => w) 1 (p (s n)) (e (s n)) (h (s n)) (u (s n)) z (t (s n))) atTop _
    simp_rw [sourceLabelRestorationRatio_single_value _ k f g _ _ _ (hh0 _) (hh _) _ q τ v w z hz hz0 hz1]
    exact tendsto_const_nhds

def scalarRestorationSingleMoment (f v w : ℝ →ᵇ ℝ) (j : ℕ) :
    Matrix (Fin (1+j)) (Fin (1+j)) ℝ →ᵇ ℝ :=
  freshMarkedMatrixKernel (gaussianMixedTest (labelRestoredFunctions f (fun _ : Fin 1 => v) j)) *
    freshMarkedMatrixKernel (gaussianMixedTest (labelRestoredFunctions f (fun _ : Fin 1 => w) j))

lemma restorationBlockTest_one (r j : ℕ) :
    restorationBlockTest r 1 j=(1 : CompactBlock CompactOverlap (r+j) →ᵇ ℝ) := by
  induction j with
  | zero => rfl
  | succ j hj => ext Q; change restorationBlockTest r 1 j _=1; rw [hj]; rfl

lemma jointRestorationBlockTest_one (r j : ℕ) :
    jointRestorationBlockTest r 1 j=(1 : CompactBlock CompactJointOverlap (r+j) →ᵇ ℝ) := by
  induction j with
  | zero => rfl
  | succ j hj => ext Q; change jointRestorationBlockTest r 1 j _=1; rw [hj]; rfl

lemma scalarRestorationSingleMoment_compact (f v w : ℝ →ᵇ ℝ)
    (j : ℕ) (Q : CompactBlock CompactOverlap (1+j)) :
    scalarRestorationSingleMoment f v w j (fun i l => (Q i l).val) =
      (restorationBlockTest 1 1 j *
        freshMarkedCompactBlockKernel (restorationMarkTest 1 f (gaussianMixedTest (fun _ => v)) j) *
        freshMarkedCompactBlockKernel (restorationMarkTest 1 f (gaussianMixedTest (fun _ => w)) j)) Q := by
  simp only [restorationBlockTest_one,one_mul,scalarRestorationSingleMoment,
    BoundedContinuousFunction.mul_apply,restorationMarkTest_gaussianMixed]
  rfl

lemma scalarRestorationSingleMoment_label {k : ℕ} (q : Fin (k+1)→Time)
    (f v w : ℝ →ᵇ ℝ) (j : ℕ)
    (Q : CompactBlock CompactJointOverlap (1+j))
    (hN : ∀ i l,(Q i l).2∈Set.range (sourceLabelLevel k)) :
    scalarRestorationSingleMoment f v w j (labelProfileGram q Q) =
      labelRestorationBlockMoment (fun i => (q i:ℝ)) f (fun _ : Fin 1 => v) (fun _ => w)
        1 j Q := by
  simp only [scalarRestorationSingleMoment,labelRestorationBlockMoment,BoundedContinuousFunction.mul_apply,
    jointRestorationBlockTest_one,one_mul,
    labelMarkedBlockKernel_profile q _ Q hN]

lemma scalarRestorationSingleMoment_diagonalMap {k : ℕ} (q : Fin (k+1)→Time)
    (f v w : ℝ →ᵇ ℝ) (j : ℕ)
    (Q : CompactArray CompactJointOverlap) (hN : CompactLabelNodes k Q) :
    scalarRestorationSingleMoment f v w j (fun i l =>
      (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal Q i l).1.val) =
      labelRestorationBlockMoment (fun i => (q i:ℝ)) f (fun _ : Fin 1 => v) (fun _ => w)
        1 j (compactBlock (1+j) Q) := by
  have he : (fun i l : Fin (1+j) => (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal Q i l).1.val)=
      labelProfileGram q (compactBlock (1+j) Q) := by
    funext i l
    simp only [compactDiagonalMapArray,labelProfileGram,Fin.val_inj]
    split_ifs <;> rfl
  rw [he]
  exact scalarRestorationSingleMoment_label q f v w j _ (fun i l => hN i l)

end SphericalPerceptronFreeEnergy
end

end OAI
