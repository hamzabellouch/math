import Mathlib
import OAI.Probability.SphericalField.Poisson.MarkMeasure

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder

section GaussianRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]

def gaussianRows (v : ι → E) : E →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => innerSL ℝ (v i))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι] in
lemma gaussianRows_apply (v : ι → E) (x : E) (i : ι) :
    gaussianRows v x i = inner ℝ (v i) x := rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma gaussianRows_adjoint_basis (v : ι → E) (i : ι) :
    (gaussianRows v).adjoint (EuclideanSpace.basisFun ι ℝ i) = v i := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [PiLp.inner_apply, gaussianRows_apply,real_inner_comm]

lemma gaussianRows_map_stdGaussian (v : ι → E) :
    (stdGaussian E).map (gaussianRows v) = multivariateGaussian 0 (Matrix.gram ℝ v) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp only [integral_id_stdGaussian,map_zero,integral_id_multivariateGaussian]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis
  intro i j
  simp only [ContinuousLinearMap.toBilinForm_apply,OrthonormalBasis.coe_toBasis]
  rw [covarianceBilin_map IsGaussian.memLp_two_id,gaussianRows_adjoint_basis,
    gaussianRows_adjoint_basis,covarianceBilin_stdGaussian,
    covarianceBilin_multivariateGaussian (Matrix.posSemidef_gram ℝ v)]
  simp
  rfl

end GaussianRows

def gaussianReplicaTest {ι : Type*} [Fintype ι] (f : ℝ →ᵇ ℝ) : EuclideanSpace ℝ ι →ᵇ ℝ :=
  ∏ i, f.compContinuous ⟨fun z => z i, by fun_prop⟩

lemma gaussianReplicaTest_apply {ι : Type*} [Fintype ι] (f : ℝ →ᵇ ℝ) (z : EuclideanSpace ℝ ι) :
    gaussianReplicaTest f z = ∏ i, f (z i) := by simp [gaussianReplicaTest]

lemma freshPattern_moment_covariance_integral
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (f : ℝ →ᵇ ℝ) (n : ℕ) :
    (∫ g, (∫ x, f (inner ℝ x g) ∂μ)^n ∂stdGaussian E) =
      ∫ xs : Fin n → E, ∫ z, gaussianReplicaTest f z
        ∂multivariateGaussian 0 (Matrix.gram ℝ xs) ∂Measure.pi (fun _ => μ) := by
  classical
  let F : (E × (Fin n → E)) →ᵇ ℝ :=
    ∏ i, f.compContinuous ⟨fun p => inner ℝ (p.2 i) p.1, by fun_prop⟩
  have hF (g : E) (xs : Fin n → E) : F (g,xs) = ∏ i, f (inner ℝ (xs i) g) := by simp [F]
  calc
    _ = ∫ g, ∫ xs : Fin n → E, F (g,xs) ∂Measure.pi (fun _ => μ) ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [hF]
      simpa only [Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι := Fin n) (fun x : E => f (inner ℝ x g)) (μ := μ)).symm
    _ = ∫ xs : Fin n → E, ∫ g, F (g,xs) ∂stdGaussian E ∂Measure.pi (fun _ => μ) :=
      integral_integral_swap (F.integrable _)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with xs
      rw [← gaussianRows_map_stdGaussian xs,
        integral_map (gaussianRows xs).continuous.measurable.aemeasurable
          (gaussianReplicaTest f).continuous.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [hF,gaussianReplicaTest_apply,gaussianRows_apply]

def gramCovariance {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ι → E) : CovarianceMatrix ι :=
  ⟨Matrix.gram ℝ v,Matrix.posSemidef_gram ℝ v⟩

lemma gramCovariance_continuous {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Continuous (gramCovariance (ι := ι) (E := E)) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).inner (continuous_apply j)

def gaussianCovarianceKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : EuclideanSpace ℝ ι →ᵇ ℝ) : CovarianceMatrix ι →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun C => ∫ z, f z ∂multivariateGaussian 0 C.val,
      (gaussianCovariance_integral_continuous f).comp (continuous_const.prodMk continuous_id)⟩
    (2*‖f‖) (by
      intro C D
      calc
        dist (∫ z, f z ∂multivariateGaussian 0 C.val) (∫ z, f z ∂multivariateGaussian 0 D.val) ≤
            ‖∫ z, f z ∂multivariateGaussian 0 C.val‖ + ‖∫ z, f z ∂multivariateGaussian 0 D.val‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_integral_le_norm _) (f.norm_integral_le_norm _)
        _ = 2*‖f‖ := by ring)

def gramReplicaLaw {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) : ProbabilityMeasure (CovarianceMatrix (Fin n)) :=
  ⟨(Measure.pi (fun _ : Fin n => μ)).map gramCovariance, inferInstance⟩

lemma freshPattern_moment_tendsto_of_gram_laws
    {E : ℕ → Type*} [∀ N, NormedAddCommGroup (E N)] [∀ N, InnerProductSpace ℝ (E N)]
    [∀ N, FiniteDimensional ℝ (E N)] [∀ N, MeasurableSpace (E N)] [∀ N, BorelSpace (E N)]
    (μ : (N : ℕ) → Measure (E N)) [∀ N, IsProbabilityMeasure (μ N)]
    (f : ℝ →ᵇ ℝ) (n : ℕ) (ν : ProbabilityMeasure (CovarianceMatrix (Fin n)))
    (h : Tendsto (fun N => gramReplicaLaw (μ N) n) atTop (𝓝 ν)) :
    Tendsto (fun N => ∫ g, (∫ x, f (inner ℝ x g) ∂μ N)^n ∂stdGaussian (E N)) atTop
      (𝓝 (∫ C, gaussianCovarianceKernel (gaussianReplicaTest (ι := Fin n) f) C ∂ν)) := by
  have hh := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (gaussianCovarianceKernel (gaussianReplicaTest (ι := Fin n) f))).continuousAt.tendsto.comp h
  convert hh using 1
  funext N
  change (∫ g, (∫ x, f (inner ℝ x g) ∂μ N)^n ∂stdGaussian (E N)) =
    ∫ C, gaussianCovarianceKernel (gaussianReplicaTest (ι := Fin n) f) C
      ∂(Measure.pi (fun _ : Fin n => μ N)).map gramCovariance
  rw [freshPattern_moment_covariance_integral,
    integral_map gramCovariance_continuous.measurable.aemeasurable
      (gaussianCovarianceKernel (gaussianReplicaTest (ι := Fin n) f)).continuous.aestronglyMeasurable]
  rfl

open TopologicalSpace

abbrev CompactOverlap := Set.Icc (-1 : ℝ) 1
abbrev CompactJointOverlap := CompactOverlap × unitInterval
abbrev CompactArray (K : Type*) := ℕ → ℕ → K
abbrev CompactBlock (K : Type*) (n : ℕ) := Fin n → Fin n → K

def compactBlock {K : Type*} (n : ℕ) (Q : CompactArray K) : CompactBlock K n :=
  fun i j => Q i j

lemma compactBlock_continuous {K : Type*} [TopologicalSpace K] (n : ℕ) :
    Continuous (compactBlock (K := K) n) := by unfold compactBlock; fun_prop

lemma compact_array_law_subsequence {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [CompactSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ℕ → ProbabilityMeasure (CompactArray K)) :
    ∃ ν : ProbabilityMeasure (CompactArray K), ∃ s : ℕ → ℕ,
      StrictMono s ∧ Tendsto (μ ∘ s) atTop (𝓝 ν) := by
  obtain ⟨ν, -, s, hs, hμ⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (μ n))
  exact ⟨ν,s,hs,hμ⟩

lemma weak_limit_closed_full {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [HasOuterApproxClosed K]
    {μ : ℕ → ProbabilityMeasure K} {ν : ProbabilityMeasure K}
    (hμ : Tendsto μ atTop (𝓝 ν)) {F : Set K} (hF : IsClosed F)
    (hfull : ∀ n, μ n F = 1) : ν F = 1 := by
  apply le_antisymm (ProbabilityMeasure.apply_le_one _ _)
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hF
  have hf (n : ℕ) : (μ n : Measure K) F = 1 := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hfull n,ENNReal.coe_one]
  simp only [hf,limsup_const] at h
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
  exact_mod_cast h

def compactGGDefect {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] (μ : ProbabilityMeasure (CompactArray K)) (n : ℕ) (i : Fin n)
    (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ) : ℝ :=
  (n : ℝ)*(∫ Q, f (compactBlock n Q)*g (Q i n) ∂μ) -
    (∫ Q, f (compactBlock n Q) ∂μ)*(∫ Q : CompactArray K, g (Q 0 1) ∂μ) -
    ∑ j ∈ Finset.univ.erase i, ∫ Q, f (compactBlock n Q)*g (Q i j) ∂μ

lemma compactGGDefect_continuous {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] (n : ℕ) (i : Fin n)
    (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ) :
    Continuous (fun μ : ProbabilityMeasure (CompactArray K) => compactGGDefect μ n i f g) := by
  let f' : CompactArray K →ᵇ ℝ := f.compContinuous ⟨compactBlock n,compactBlock_continuous n⟩
  let g' (i j : ℕ) : CompactArray K →ᵇ ℝ := g.compContinuous ⟨fun Q => Q i j,by fun_prop⟩
  have hf := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f'
  have hg (i j : ℕ) := ProbabilityMeasure.continuous_integral_boundedContinuousFunction (g' i j)
  have hfg (i j : ℕ) := ProbabilityMeasure.continuous_integral_boundedContinuousFunction (f' * g' i j)
  exact (continuous_const.mul (hfg i n) |>.sub (hf.mul (hg 0 1))).sub
    (continuous_finsetSum _ fun j _ => hfg i j)

end SphericalPerceptron
end
end
end

end OAI
