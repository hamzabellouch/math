import OAI.Probability.InvariantIsing.Arrays.TensorGaussianMean
import OAI.Probability.InvariantIsing.Haar.HaarVariance

namespace OAI

/-! The actual finite tensor perturbation with a fixed spin/leaf prior.
The prior may be a normalized spin constraint; it is independent of the rotation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def priorTensorLog {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  Real.log (∫ x, Real.exp (rotatedEnergy eig (specialRotation p.1) x.1 + fieldEnergy c x.1 +
    cylinderField (tensorLeafCoefficients (specialRotation p.1) I degree amplitude n v x) p.2) ∂ν)

lemma measurable_priorTensorLog {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (priorTensorLog ν eig c I degree amplitude v) := by
  have hm : Measurable (fun p : (SpecialOrthogonal N × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf n) =>
      rotatedEnergy eig (specialRotation p.1.1) p.2.1 + fieldEnergy c p.2.1 +
      cylinderField (tensorLeafCoefficients (specialRotation p.1.1) I degree amplitude n v p.2) p.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hbase : Measurable (fun U : SpecialOrthogonal N =>
        rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1) := by
      exact ((Finset.measurable_sum _ fun i _ =>
        ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul
          (eig i)).const_mul (1/2 : ℝ)).add_const _
    apply (hbase.comp measurable_fst).add
    simp only [tensorLeafCoefficients, cylinderField_feature]
    apply Finset.measurable_sum
    intro i _
    exact (((measurable_spinTensorFeature I degree amplitude x.1 i.2).comp
      measurable_fst).const_mul _).mul
      ((measurable_pi_apply (treeFeatureTag n x.2 i)).comp measurable_snd)
  exact hm.exp.stronglyMeasurable.integral_prod_right'.measurable.log

lemma priorTensorLog_gaussian_memLp {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : Fin (n+1) → ℝ≥0) (monomial : Fin (n+1) → Fin k → ℝ≥0)
    (U : SpecialOrthogonal N) :
    MemLp (fun z => priorTensorLog ν eig c I degree amplitude
      (fun i => tensorVarianceProfile I degree (site i) (monomial i)) (U,z)) 2 gaussianCoordinates := by
  have hi := cylinder_log_partition_memLp_two ν
    (fun x => rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1)
    (finite_spin_base_exp_integrable ν
      (fun σ => rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ))
    (tensorLeafCoefficients (specialRotation U) I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i)))
    (tensorLeafCoefficients_variance_le (specialRotation U) I degree amplitude n site monomial) 1
  simpa only [one_mul,priorTensorLog] using hi

lemma priorTensorLog_gaussian_variance (hgauss : GaussianLipschitzVarianceInput)
    {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : Fin (n+1) → ℝ≥0) (monomial : Fin (n+1) → Fin k → ℝ≥0)
    (U : SpecialOrthogonal N) :
    variance (fun z => priorTensorLog ν eig c I degree amplitude
      (fun i => tensorVarianceProfile I degree (site i) (monomial i)) (U,z)) gaussianCoordinates ≤
      ∑ i, ((site i : ℝ)*N + ∑ j, (monomial i j : ℝ)*amplitude j^2) := by
  have hv := countable_cylinder_log_partition_variance_le hgauss ν
    (fun x => rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1)
    (finite_spin_base_exp_integrable ν
      (fun σ => rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ))
    (tensorLeafCoefficients (specialRotation U) I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i)))
    _ (by positivity)
    (tensorLeafCoefficients_variance_le (specialRotation U) I degree amplitude n site monomial) 1
  simpa only [one_pow, one_mul,priorTensorLog] using hv

/-- The variance constant is independent of the mass and cardinality of
an imposed spin constraint. -/
theorem priorTensorLog_variance (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 3≤N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m k n : ℕ, ∀ ν : Measure (Spin N × LabeledLeaf n), IsProbabilityMeasure ν →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0<K → (∀ i, |eig i|≤K) →
    ∀ I : Fin m → Finset (Fin N), ∀ degree : Fin k → Fin m → ℕ,
    ∀ amplitude : Fin k → ℝ, ∀ site : Fin (n+1) → ℝ≥0,
    ∀ monomial : Fin (n+1) → Fin k → ℝ≥0,
      let F := priorTensorLog ν eig c I degree amplitude
        (fun i => tensorVarianceProfile I degree (site i) (monomial i))
      let L := K*N + 2*(∑ i : Fin (n+1), ∑ j, (monomial i j : ℝ)*amplitude j^2*
        ∑ a, (degree j a : ℝ))
      MemLp F 2 (μ.prod gaussianCoordinates) ∧
        variance F (μ.prod gaussianCoordinates) ≤
          (∑ i, ((site i : ℝ)*N + ∑ j, (monomial i j : ℝ)*amplitude j^2)) + C*L^2/N := by
  obtain ⟨C,hC,hvar⟩ := haar_frobeniusLipschitz_variance hhaar
  refine ⟨C,hC,?_⟩
  intro N hN μ hμ hμinv m k n ν hν eig c K hK heig I degree amplitude site monomial F L
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure ν := hν
  let M := fun U => ∫ z, F (U,z) ∂gaussianCoordinates
  have hm : Measurable M := (measurable_priorTensorLog ν eig c I degree amplitude _).stronglyMeasurable
    |>.integral_prod_right' |>.measurable
  have hL : 0<L := by
    dsimp only [L]
    exact add_pos_of_pos_of_nonneg (mul_pos hK (by exact_mod_cast (show 0<N by omega))) (by positivity)
  have hLip : ∀ U V, |M U-M V|≤L*frobeniusDistance U V := fun U V =>
    tensorLeafLogMean_abs_sub_le (by omega) eig c U V K hK.le heig I degree amplitude n site monomial ν
  have hM := haar_frobeniusLipschitz_memLp_two hhaar N hN μ hμinv M hm L hL hLip
  have hlocal U := priorTensorLog_gaussian_memLp ν eig c I degree amplitude site monomial U
  have hlocalVar U := priorTensorLog_gaussian_variance hgauss ν eig c I degree amplitude site monomial U
  have hresult := variance_of_conditional_center μ gaussianCoordinates
    (measurable_priorTensorLog ν eig c I degree amplitude _) hM
    (fun U => ((hlocal U).sub (memLp_const (M U))).integrable_sq) (fun _ => rfl)
    (fun U => by
      rw [← variance_eq_integral (hlocal U).aestronglyMeasurable.aemeasurable]
      exact hlocalVar U)
  exact ⟨hresult.1,hresult.2.trans (add_le_add le_rfl
    (hvar N hN μ hμ hμinv M hm L hL hLip))⟩

end InvariantIsing

end

end OAI
