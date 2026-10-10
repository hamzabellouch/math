import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkRadialIdentity

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction BigOperators Matrix

lemma bulk_single_mean_of_L2 (N M : ℕ→ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ) (c : ℝ)
    (hl : Tendsto (fun n=>bulkReplicaMean (N n) (M n) f (v n) 1
      (fun a x=>(bulkSingleAverage (N n) (M n) w a x-c)^2)) atTop (𝓝 0)) :
    Tendsto (fun n=>bulkReplicaMean (N n) (M n) f (v n) 1
      (bulkSingleAverage (N n) (M n) w)) atTop (𝓝 c) :=
  bulkReplicaMean_L2_tendsto N M f v 1 (fun n=>bulkSingleAverage (N n) (M n) w)
    (fun n=>bulkSingleAverage_measurable _ _ _) (fun n=>(M n:ℝ)/(N n+1:ℕ)*‖w‖)
    (fun n=>by positivity) (fun n=>bulkSingleAverage_bound _ _ _) c hl

lemma bulk_diagonal_mean_add (n M : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) :
    bulkReplicaMean n M f.f v 1 (fun a x=>bulkC (n+1) M f a.1 (x 0)+
      bulkB (n+1) M f a.1 (x 0) (x 0))=
    bulkReplicaMean n M f.f v 1 (bulkSingleAverage n M (f.dilationMark hf))+
      bulkReplicaMean n M f.f v 1 (bulkSingleAverage n M (f.d1*f.d1)) := by
  change bulkReplicaMean n M f.f v 1 (fun a x=>bulkSingleAverage n M (f.dilationMark hf) a x+
      bulkSingleAverage n M (f.d1*f.d1) a x)=_
  exact bulkReplicaMean_add_bounded n M 1 f.f v _ _
    (bulkSingleAverage_measurable _ _ _) (bulkSingleAverage_measurable _ _ _) _ _
    (bulkSingleAverage_bound _ _ _) (bulkSingleAverage_bound _ _ _)

lemma bulk_radial_limit_relation (N M : ℕ→ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℕ→ℝ) (c d : ℝ)
    (hc : Tendsto (fun n=>bulkReplicaMean (N n) (M n) f.f (v n) 1
      (fun a x=>(bulkC (N n+1) (M n) f a.1 (x 0)-c)^2)) atTop (𝓝 0))
    (hd : Tendsto (fun n=>bulkReplicaMean (N n) (M n) f.f (v n) 1
      (fun a x=>(bulkB (N n+1) (M n) f a.1 (x 0) (x 0)-d)^2)) atTop (𝓝 0))
    (K : ℝ) (hK : ∀ n,(M n:ℝ)/(N n+1:ℕ)*‖f.d1‖^2≤K)
    (μ : ProbabilityMeasure (BulkPairRange K))
    (hl : Tendsto (fun n=>bulkPairLaw (N n) (M n) f.f f.d1 (v n) K (hK n)) atTop (𝓝 μ)) :
    c+d=∫ p,p.1.val*p.2.val ∂(μ : Measure (BulkPairRange K)) := by
  have hcm := bulk_single_mean_of_L2 N M f.f (f.dilationMark hf) v c hc
  have hdm := bulk_single_mean_of_L2 N M f.f (f.d1*f.d1) v d hd
  have hs := hcm.add hdm
  have he n := bulk_diagonal_mean_add (N n) (M n) f hf (v n)
  simp_rw [←he,bulk_radial_sum_identity _ _ f hf] at hs
  let F : BulkPairRange K→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨fun p=>p.1.val*p.2.val,by fun_prop⟩
  have ht := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).continuousAt.tendsto.comp hl
  have htest n : (∫ p,F p ∂(bulkPairLaw (N n) (M n) f.f f.d1 (v n) K (hK n) : Measure _))=
      bulkReplicaMean (N n) (M n) f.f (v n) 2
        (fun a x=>spinOverlap (x 0) (x 1)*bulkB (N n+1) (M n) f a.1 (x 0) (x 1)) := by
    rw [bulkPairLaw_integral]
    congr 1
    funext a x
    change spinOverlap (x 1) (x 0)*bulkPairAverage (N n) (M n) f.d1 a x=_
    rw [←bulkB_pairAverage]
    congr 1
    exact real_inner_comm _ _
  change Tendsto (fun n=>∫ p,F p ∂(bulkPairLaw (N n) (M n) f.f f.d1 (v n) K (hK n) : Measure _)) atTop _ at ht
  simp_rw [htest] at ht
  exact tendsto_nhds_unique hs ht

lemma isClosed_covarianceMatrix {I : Type*} [Fintype I] [DecidableEq I] :
    IsClosed {M : Matrix I I ℝ | M.PosSemidef} := by
  have he : {M : Matrix I I ℝ | M.PosSemidef} =
      {M : Matrix I I ℝ | ∀ i j, M j i=M i j} ∩ ⋂ x : I → ℝ,
        {M : Matrix I I ℝ | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp only [mem_ofPred_eq,mem_inter_iff,mem_iInter,Matrix.posSemidef_iff_dotProduct_mulVec,
      Matrix.IsHermitian.ext_iff,star_trivial]
  rw [he]
  apply IsClosed.inter
  · simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  · exact isClosed_iInter fun x => isClosed_le continuous_const (by
      unfold dotProduct Matrix.mulVec
      fun_prop)

private lemma cavity_extension_exists {I : Type*} [Fintype I] [DecidableEq I]
    (Ψ : EuclideanSpace ℝ I →ᵇ ℝ) :
    ∃ F : Matrix I I ℝ →ᵇ ℝ,
      ‖F‖=‖gaussianCovarianceKernel Ψ‖ ∧
      ∀ C : CovarianceMatrix I, F C.val=gaussianCovarianceKernel Ψ C := by
  let : NormalSpace (Matrix I I ℝ) := inferInstanceAs (NormalSpace (I→I→ℝ))
  obtain ⟨F,hF,he⟩ := (gaussianCovarianceKernel Ψ).exists_extension_norm_eq_of_isClosedEmbedding
    isClosed_covarianceMatrix.isClosedEmbedding_subtypeVal
  exact ⟨F,hF,fun C => congrFun he C⟩

def cavityMatrixKernel {I : Type*} [Fintype I] [DecidableEq I]
    (Ψ : EuclideanSpace ℝ I →ᵇ ℝ) : Matrix I I ℝ →ᵇ ℝ :=
  Classical.choose (cavity_extension_exists Ψ)

lemma cavityMatrixKernel_posSemidef {I : Type*} [Fintype I] [DecidableEq I]
    (Ψ : EuclideanSpace ℝ I →ᵇ ℝ) (C : Matrix I I ℝ) (hC : C.PosSemidef) :
    cavityMatrixKernel Ψ C=∫ z,Ψ z ∂multivariateGaussian 0 C :=
  (Classical.choose_spec (cavity_extension_exists Ψ)).2 ⟨C,hC⟩

lemma sphericalExp_continuous (n : ℕ) (R : ℝ) : Continuous (fun x => sphericalExp n x R) := by
  have h : (fun x => sphericalExp n x R) = fun x => Real.exp (logSphericalExp n R x) := by
    ext x
    exact (Real.exp_log ((by norm_num : (0:ℝ)<1).trans_le (one_le_sphericalExp n x R))).symm
  rw [h]
  exact (logSphericalExp_lipschitz n R).continuous.rexp

def cappedSphericalExp (n : ℕ) (R Λ : ℝ) (hΛ : 1≤Λ) : Spin (n+1) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (sphericalExp n x R) Λ,(sphericalExp_continuous n R).min continuous_const⟩
    (2*Λ) (by
      intro x y
      have hx : 1 ≤ min (sphericalExp n x R) Λ := le_min (one_le_sphericalExp n x R) hΛ
      have hy : 1 ≤ min (sphericalExp n y R) Λ := le_min (one_le_sphericalExp n y R) hΛ
      change |min (sphericalExp n x R) Λ-min (sphericalExp n y R) Λ|≤2*Λ
      exact abs_le.mpr ⟨by linarith [min_le_right (sphericalExp n y R) Λ],
        by linarith [min_le_right (sphericalExp n x R) Λ]⟩)

abbrev CavityReplicaIndex (n d r : ℕ) := (Fin (n+1) ⊕ Fin d) × Fin r

def cavityVectorProjection (n d r : ℕ) (j : Fin r) :
    C(EuclideanSpace ℝ (CavityReplicaIndex n d r),Spin (n+1)) :=
  ⟨fun z => WithLp.toLp 2 (fun i => z (Sum.inl i,j)),by fun_prop⟩

def cavityReplicaTest (n d r : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ) :
    EuclideanSpace ℝ (CavityReplicaIndex n d r) →ᵇ ℝ :=
  ∏ j : Fin r,
    (cappedSphericalExp n (Real.sqrt (n+1:ℕ)) Λ hΛ).compContinuous (cavityVectorProjection n d r j) *
      ∏ t : Fin d,(expBCF 1 f).compContinuous ⟨fun z => z (Sum.inr t,j),by fun_prop⟩

lemma cavityReplicaTest_apply (n d r : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (z : EuclideanSpace ℝ (CavityReplicaIndex n d r)) :
    cavityReplicaTest n d r f Λ hΛ z =
      ∏ j : Fin r, min (sphericalExp n (WithLp.toLp 2 (fun i => z (Sum.inl i,j)))
        (Real.sqrt (n+1:ℕ))) Λ * ∏ t : Fin d,Real.exp (f (z (Sum.inr t,j))) := by
  simp [cavityReplicaTest,cappedSphericalExp,cavityVectorProjection,expBCF]

def cavityBlockCovariance (n d r : ℕ) {K : ℝ} (Q : CompactArray (BulkPairRange K)) :
    Matrix (CavityReplicaIndex n d r) (CavityReplicaIndex n d r) ℝ :=
  fun i j => if i.1=j.1 then
    Sum.elim (fun _ => (Q i.2 j.2).2.val) (fun _ => (Q i.2 j.2).1.val) i.1 else 0

lemma cavityBlockCovariance_continuous (n d r : ℕ) (K : ℝ) :
    Continuous (cavityBlockCovariance n d r (K:=K)) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold cavityBlockCovariance
  split_ifs
  · cases i.1 <;> dsimp only [Sum.elim] <;> fun_prop
  · exact continuous_const

def cavityArrayKernel (n d r : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ) :
    CompactArray (BulkPairRange K) →ᵇ ℝ :=
  (cavityMatrixKernel (cavityReplicaTest n d r f Λ hΛ)).compContinuous
    ⟨cavityBlockCovariance n d r,cavityBlockCovariance_continuous n d r K⟩

lemma cavityArrayKernel_tendsto (n d r : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ)
    {ν : ℕ→ProbabilityMeasure (CompactArray (BulkPairRange K))}
    {ν₀ : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hν : Tendsto ν atTop (𝓝 ν₀)) :
    Tendsto (fun j => ∫ Q,cavityArrayKernel n d r f Λ hΛ K Q ∂ν j) atTop
      (𝓝 (∫ Q,cavityArrayKernel n d r f Λ hΛ K Q ∂ν₀)) :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (cavityArrayKernel n d r f Λ hΛ K)).continuousAt.tendsto.comp hν

end SphericalPerceptronFreeEnergy
end

end OAI
