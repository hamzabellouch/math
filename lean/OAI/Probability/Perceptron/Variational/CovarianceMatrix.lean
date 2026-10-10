import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder

abbrev CovarianceMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] := {C : Matrix ι ι ℝ // C.PosSemidef}

instance covarianceMatrixMeasurableSpace (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MeasurableSpace (CovarianceMatrix ι) :=
  inferInstanceAs (MeasurableSpace {C : ι → ι → ℝ // Matrix.PosSemidef C})

instance covarianceMatrixBorelSpace (ι : Type*) [Fintype ι] [DecidableEq ι] :
    BorelSpace (CovarianceMatrix ι) :=
  inferInstanceAs (BorelSpace {C : ι → ι → ℝ // Matrix.PosSemidef C})

def gaussianCovarianceLaw {ι : Type*} [Fintype ι] [DecidableEq ι] (p : EuclideanSpace ℝ ι × CovarianceMatrix ι) :
    ProbabilityMeasure (EuclideanSpace ℝ ι) := ⟨multivariateGaussian p.1 p.2.val, inferInstance⟩

lemma gaussianCovarianceLaw_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (gaussianCovarianceLaw (ι := ι)) := by
  classical
  have : SequentialSpace (EuclideanSpace ℝ ι × CovarianceMatrix ι) :=
    inferInstanceAs (SequentialSpace (EuclideanSpace ℝ ι × {C : ι → ι → ℝ // Matrix.PosSemidef C}))
  rw [continuous_iff_seqContinuous]
  intro p p₀ hp
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  change Tendsto (fun n => charFun (multivariateGaussian (p n).1 (p n).2.val) t) atTop
    (𝓝 (charFun (multivariateGaussian p₀.1 p₀.2.val) t))
  simp_rw [charFun_multivariateGaussian (p _).2.property,charFun_multivariateGaussian p₀.2.property]
  have hc : Continuous (fun q : EuclideanSpace ℝ ι × CovarianceMatrix ι =>
      Complex.exp (((inner ℝ t q.1 : ℝ) : ℂ)*Complex.I -
        ((∑ i, t i * ∑ j, q.2.val i j * t j : ℝ) : ℂ)/2)) := by
    have he (i j : ι) : Continuous (fun q : EuclideanSpace ℝ ι × CovarianceMatrix ι => q.2.val i j) :=
      (show Continuous (fun q : EuclideanSpace ℝ ι × CovarianceMatrix ι => q.2.val) from
        continuous_subtype_val.comp continuous_snd).matrix_elem i j
    have hi : Continuous (fun q : EuclideanSpace ℝ ι × CovarianceMatrix ι => inner ℝ t q.1) :=
      continuous_const.inner continuous_fst
    exact ((Complex.continuous_ofReal.comp hi).mul continuous_const |>.sub
      ((Complex.continuous_ofReal.comp (continuous_finsetSum _ fun i _ => continuous_const.mul
        (continuous_finsetSum _ fun j _ => (he i j).mul continuous_const))).div_const 2)).cexp
  exact hc.continuousAt.tendsto.comp hp

lemma gaussianCovariance_integral_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : EuclideanSpace ℝ ι →ᵇ ℝ) :
    Continuous (fun p : EuclideanSpace ℝ ι × CovarianceMatrix ι =>
      ∫ x, f x ∂multivariateGaussian p.1 p.2.val) :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp gaussianCovarianceLaw_continuous

lemma gaussianCovariance_integral_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ → EuclideanSpace ℝ ι} {m₀ : EuclideanSpace ℝ ι}
    {C : ℕ → CovarianceMatrix ι} {C₀ : CovarianceMatrix ι}
    (hm : Tendsto m atTop (𝓝 m₀)) (hC : Tendsto C atTop (𝓝 C₀))
    (f : EuclideanSpace ℝ ι →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f x ∂multivariateGaussian (m n) (C n).val) atTop
      (𝓝 (∫ x, f x ∂multivariateGaussian m₀ C₀.val)) :=
  (gaussianCovariance_integral_continuous f).continuousAt.tendsto.comp (hm.prodMk_nhds hC)

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
  ⟨(Measure.pi (fun _ : Fin n => μ)).map gramCovariance,
    inferInstance⟩

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

lemma compactGGDefect_limit {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] {μ : ℕ → ProbabilityMeasure (CompactArray K)}
    {ν : ProbabilityMeasure (CompactArray K)} (hμ : Tendsto μ atTop (𝓝 ν))
    (n : ℕ) (i : Fin n) (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ)
    (hdef : Tendsto (fun k => compactGGDefect (μ k) n i f g) atTop (𝓝 0)) :
    compactGGDefect ν n i f g = 0 :=
  tendsto_nhds_unique ((compactGGDefect_continuous n i f g).continuousAt.tendsto.comp hμ) hdef

lemma compactGG_joint_law {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K)) {n : ℕ} (hn : 0 < n) (i : Fin n)
    (hGG : ∀ (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ), compactGGDefect μ n i f g = 0) :
    (μ : Measure (CompactArray K)).map (fun Q => (compactBlock n Q, Q i n)) =
      ((n : ℝ≥0)⁻¹) •
        (((μ : Measure (CompactArray K)).map (compactBlock n)).prod
            ((μ : Measure (CompactArray K)).map (fun Q => Q 0 1)) +
          ∑ j ∈ Finset.univ.erase i,
            (μ : Measure (CompactArray K)).map (fun Q => (compactBlock n Q, Q i j))) := by
  classical
  have hb := (compactBlock_continuous (K := K) n).measurable
  have he (k l : ℕ) : Measurable (fun Q : CompactArray K => Q k l) := by fun_prop
  apply Measure.ext_of_integral_mul_boundedContinuousFunction
  intro f g
  let F : (CompactBlock K n × K) →ᵇ ℝ :=
    (f.compContinuous ⟨Prod.fst,continuous_fst⟩) * (g.compContinuous ⟨Prod.snd,continuous_snd⟩)
  have hF : ∀ ρ : Measure (CompactBlock K n × K), IsFiniteMeasure ρ → Integrable F ρ := by
    intro ρ hρ
    exact F.integrable ρ
  change ∫ p, F p ∂_ = ∫ p, F p ∂_
  rw [integral_smul_nnreal_measure,integral_add_measure (hF _ inferInstance) (hF _ inferInstance),
    integral_finsetSum_measure]
  · simp_rw [integral_map (hb.prodMk (he _ _)).aemeasurable F.continuous.aestronglyMeasurable]
    simp only [F,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk,NNReal.smul_def,NNReal.coe_inv,NNReal.coe_natCast,smul_eq_mul]
    rw [integral_prod_mul,integral_map hb.aemeasurable f.continuous.aestronglyMeasurable,
      integral_map (he 0 1).aemeasurable g.continuous.aestronglyMeasurable]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have h := hGG f g
    unfold compactGGDefect at h
    apply (mul_right_inj' hn').mp
    rw [←mul_assoc,mul_inv_cancel₀ hn',one_mul]
    linarith [h]
  · intro j hj
    exact hF _ inferInstance

open scoped Polynomial

lemma integral_continuous_tendsto_of_moments {a b : ℝ}
    (μ : ℕ → Measure (Icc a b)) (ν : Measure (Icc a b))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (h : ∀ k : ℕ, Tendsto (fun n => ∫ x, (x.val)^k ∂μ n) atTop
      (𝓝 (∫ x, (x.val)^k ∂ν))) (f : C(Icc a b, ℝ)) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hi (ρ : Measure (Icc a b)) [IsFiniteMeasure ρ] (p : ℝ[X]) :
      Integrable (fun x : Icc a b => p.eval x.val) ρ :=
    (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp (p : ℝ[X]) : Tendsto (fun n => ∫ x, p.eval x.val ∂μ n) atTop
      (𝓝 (∫ x, p.eval x.val ∂ν)) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simpa only [Polynomial.eval_add,integral_add (hi _ p) (hi _ q)] using hp.add hq
    | monomial k c =>
      simpa only [Polynomial.eval_monomial,integral_const_mul] using tendsto_const_nhds.mul (h k)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨p, hpε⟩ := exists_polynomial_near_continuousMap a b f (ε/3) (by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hp p)) (ε/3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbnd (ρ : Measure (Icc a b)) [IsProbabilityMeasure ρ] :
      |(∫ x, p.eval x.val ∂ρ) - ∫ x, f x ∂ρ| < ε/3 := by
    rw [← integral_sub (hi ρ p) (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    · calc
        |∫ x, p.eval x.val - f x ∂ρ| ≤ ‖p.toContinuousMapOn (Icc a b)-f‖ := by
          simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one,Real.norm_eq_abs,ContinuousMap.sub_apply,Polynomial.toContinuousMapOn_apply,Polynomial.toContinuousMap_apply] using
            (norm_integral_le_of_norm_le_const (μ := ρ)
              (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm
                (p.toContinuousMapOn (Icc a b)-f) x))
        _ < ε/3 := hpε
  have h₁ := hbnd (μ n)
  have h₂ := hbnd ν
  have h₃ := hN n hn
  rw [Real.dist_eq] at h₃ ⊢
  calc
    |(∫ x, f x ∂μ n) - ∫ x, f x ∂ν| ≤
        |(∫ x, f x ∂μ n) - ∫ x, p.eval x.val ∂μ n| +
        |(∫ x, p.eval x.val ∂μ n) - ∫ x, p.eval x.val ∂ν| +
        |(∫ x, p.eval x.val ∂ν) - ∫ x, f x ∂ν| := by
          calc
            _ ≤ |(∫ x, f x ∂μ n) - ∫ x, p.eval x.val ∂μ n| +
                |(∫ x, p.eval x.val ∂μ n) - ∫ x, f x ∂ν| := abs_sub_le _ _ _
            _ ≤ _ := by
              linarith [abs_sub_le (∫ x, p.eval x.val ∂μ n)
                (∫ x, p.eval x.val ∂ν) (∫ x, f x ∂ν)]
    _ < ε := by rw [abs_sub_comm (∫ x, f x ∂μ n)] ; linarith

lemma trial_integrable (m : Trial) : Integrable m timeLaw := by
  change Integrable m (volume : Measure Time)
  apply (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (m.nonneg t)]
    exact m.le_one t

lemma tailIntegral_mono {m n : Trial} (h : ∀ t, m t ≤ n t) (t : Time) :
    tailIntegral m t ≤ tailIntegral n t :=
  integral_mono (trial_integrable m).integrableOn (trial_integrable n).integrableOn h

lemma entropy_antitone {m n : Trial} (h : ∀ t, m t ≤ n t) : entropy n ≤ entropy m := by
  apply ENNReal.div_le_div_right
  apply lintegral_mono
  intro t
  exact tsub_le_tsub_right (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (tailIntegral_mono h t))) _

def upperRoundedTrial (m : Trial) (n : ℕ) : Trial where
  toFun := fun t => (⌈((n+1 : ℕ) : ℝ)*m t⌉₊ : ℝ) / (n+1 : ℕ)
  monotone := by
    intro s t hst
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_left (m.monotone hst) (by positivity))
  measurable :=
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (Nat.measurable_ceil.comp (measurable_const.mul m.measurable))).div_const _
  nonneg := by intro t; positivity
  le_one := by
    intro t
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast (Nat.ceil_le.mpr (show (((n+1 : ℕ) : ℝ)*m t) ≤ ((n+1 : ℕ) : ℝ) by
      nlinarith [m.le_one t]))

lemma le_upperRoundedTrial (m : Trial) (n : ℕ) (t : Time) : m t ≤ upperRoundedTrial m n t := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n+1 : ℕ))).mpr
  simpa only [mul_comm] using (Nat.le_ceil (((n+1 : ℕ) : ℝ)*m t))

lemma upperRoundedTrial_sub_le (m : Trial) (n : ℕ) (t : Time) :
    upperRoundedTrial m n t - m t ≤ 1/((n+1 : ℕ) : ℝ) := by
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ)*m t from mul_nonneg (by positivity) (m.nonneg t))
  change (⌈((n+1 : ℕ) : ℝ)*m t⌉₊ : ℝ) / (n+1 : ℕ) - m t ≤ _
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n+1 : ℕ))).mpr
  have hn : (((n+1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp
  nlinarith

lemma upperRoundedTrial_finite_range (m : Trial) (n : ℕ) :
    (Set.range (upperRoundedTrial m n)).Finite := by
  apply (Set.finite_Iic (n+1)).image (fun k : ℕ => (k : ℝ)/((n+1 : ℕ) : ℝ)) |>.subset
  rintro _ ⟨t,rfl⟩
  refine ⟨⌈((n+1 : ℕ) : ℝ)*m t⌉₊, ?_, rfl⟩
  exact Nat.ceil_le.mpr (by nlinarith [m.le_one t])

def terminalTrial (m : Trial) (r : Time) : Trial where
  toFun := fun t => if r ≤ t then 1 else m t
  monotone := by
    intro s t hst
    by_cases hs : r ≤ s
    · simp only [ite_eq_left hs,ite_eq_left (hs.trans hst)]
      exact le_rfl
    · by_cases ht : r ≤ t
      · simpa only [ite_eq_right hs,ite_eq_left ht] using m.le_one s
      · simpa only [ite_eq_right hs,ite_eq_right ht] using m.monotone hst
  measurable := Measurable.ite measurableSet_Ici measurable_const m.measurable
  nonneg := by intro t; split_ifs; norm_num; exact m.nonneg t
  le_one := by intro t; split_ifs; exact le_rfl; exact m.le_one t

end SphericalPerceptronFreeEnergy

end

end OAI
