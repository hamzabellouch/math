import Mathlib
import OAI.NumberTheory.PrimePackets.CoordinateLattices

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
namespace PrimeDegreePackets
open ThetaConstruction
variable {n : ℕ} {K : Type*} [Field K] [NumberField K]

def fullLatticeEuclideanBasis (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (embeddingMatrix M σ).transpose
    (isUnit_iff_ne_zero.mpr (by simpa only [Matrix.det_transpose] using embeddingMatrix_det_ne_zero M σ hn))).toContinuousLinearEquiv

lemma fullLatticeEuclideanBasis_det (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) :
    LinearMap.det (fullLatticeEuclideanBasis M σ hn).toLinearMap = (embeddingMatrix M σ).det := by
  change LinearMap.det ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) (embeddingMatrix M σ).transpose) = _
  rw [LinearMap.det_toLin,Matrix.det_transpose]

lemma fullLatticeEuclideanBasis_apply (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) (z : Fin n → ℤ) :
    fullLatticeEuclideanBasis M σ hn (euclideanInteger z) =
      toLp 2 (fun j => σ j (M.basis.equivFun.symm z : K)) := by
  change ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) (embeddingMatrix M σ).transpose) _ = _
  rw [Matrix.toLin_apply]
  ext j
  simp [EuclideanSpace.basisFun_apply,Pi.single_apply,Matrix.mulVec,
    dotProduct,euclideanInteger,integerVector,embeddingMatrix,Module.Basis.equivFun_symm_apply,
    map_sum,mul_comm]

def fullLatticeTheta (M : FullLattice n K) (σ : OrderedEmbeddings n K) (t : ℝ) : ℂ :=
  ∑' a : M.carrier, Complex.exp (-(t:ℂ) * ‖toLp 2 (fun j => σ j (a:K))‖^2)

lemma fullLatticeTheta_eq (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) (t : ℝ) :
    fullLatticeTheta M σ t = latticeTheta (fullLatticeEuclideanBasis M σ hn) t := by
  symm
  unfold latticeTheta fullLatticeTheta
  simp_rw [fullLatticeEuclideanBasis_apply]
  exact M.basis.equivFun.symm.toEquiv.tsum_eq (fun a : M.carrier =>
    Complex.exp (-(t:ℂ) * ‖toLp 2 (fun j => σ j (a:K))‖^2))

 

theorem fullLatticeTheta_inversion (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) (t : ℝ) (ht : 0 < t) :
    fullLatticeTheta M σ t = (((|(embeddingMatrix M σ).det⁻¹|:ℝ):ℂ) *
      (Real.pi/(t:ℂ)) ^ ((n:ℂ)/2)) *
      latticeTheta (adjointEquiv (fullLatticeEuclideanBasis M σ hn).symm) (Real.pi^2/t) := by
  rw [fullLatticeTheta_eq M σ hn,latticeTheta_inversion _ t ht,fullLatticeEuclideanBasis_det]
  simp

end PrimeDegreePackets


namespace PrimeDegreePackets
open ThetaConstruction
variable {n : ℕ} {K : Type*} [Field K] [NumberField K]

lemma sum_orderedEmbeddings (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) (a : K) :
    ∑ i, σ i a = (Algebra.trace ℚ K a : ℝ) := by
  apply Complex.ofReal_injective
  have h := trace_eq_sum_embeddings (K := ℚ) ℂ (x := a)
  rw [← (orderedComplexEmbeddings σ hn).sum_comp] at h
  change (algebraMap ℚ ℂ) (Algebra.trace ℚ K a) = ∑ i, Complex.ofReal (σ i a) at h
  rw [← Complex.ofReal_sum] at h
  change (Algebra.trace ℚ K a : ℂ) = _ at h
  simpa only [Complex.ofReal_ratCast] using h.symm

def traceDualFullLattice (M : FullLattice n K) (hn : finrank ℚ K = n) : FullLattice n K where
  carrier := Submodule.span ℤ (Set.range ((Algebra.traceForm ℚ K).dualBasis
    (traceForm_nondegenerate ℚ K) (fullLatticeRatBasis M hn)))
  basis := Basis.span (((Algebra.traceForm ℚ K).dualBasis
    (traceForm_nondegenerate ℚ K) (fullLatticeRatBasis M hn)).linearIndependent.restrict_scalars' ℤ)
  spans := by
    rw [Submodule.span_span_of_tower, Basis.span_eq]

lemma traceDualFullLattice_basis (M : FullLattice n K) (hn : finrank ℚ K = n) (i : Fin n) :
    ((traceDualFullLattice M hn).basis i : K) =
      (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (fullLatticeRatBasis M hn) i := by
  exact Basis.coe_span_apply (((Algebra.traceForm ℚ K).dualBasis
    (traceForm_nondegenerate ℚ K) (fullLatticeRatBasis M hn)).linearIndependent.restrict_scalars' ℤ) i

lemma traceDualFullLattice_carrier (M : FullLattice n K) (hn : finrank ℚ K = n) :
    (traceDualFullLattice M hn).carrier = (Algebra.traceForm ℚ K).dualSubmodule M.carrier := by
  rw [← fullLattice_span_basis M]
  simpa only [traceDualFullLattice,← fullLatticeRatBasis_apply M hn] using
    ((Algebra.traceForm ℚ K).dualSubmodule_span_of_basis
      (traceForm_nondegenerate ℚ K) (fullLatticeRatBasis M hn)).symm

lemma traceDual_embeddingMatrix_mul (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : finrank ℚ K = n) :
    embeddingMatrix (traceDualFullLattice M hn) σ * (embeddingMatrix M σ).transpose = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply,embeddingMatrix,Matrix.transpose_apply,← map_mul]
  rw [sum_orderedEmbeddings σ hn]
  have h := (Algebra.traceForm ℚ K).apply_dualBasis_left
    (traceForm_nondegenerate ℚ K) (fullLatticeRatBasis M hn) i j
  rw [traceDualFullLattice_basis]
  simp only [Algebra.traceForm_apply,fullLatticeRatBasis_apply] at h
  rw [h]
  by_cases hij : i = j
  · subst j; simp
  · simp [hij,Ne.symm hij]

lemma fullLatticeEuclideanBasis_toLinearMap (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : finrank ℚ K = n) :
    (fullLatticeEuclideanBasis M σ hn).toLinearMap = Matrix.toLin
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (embeddingMatrix M σ).transpose := rfl

lemma traceDualFullLattice_euclideanBasis (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : finrank ℚ K = n) :
    fullLatticeEuclideanBasis (traceDualFullLattice M hn) σ hn =
      adjointEquiv (fullLatticeEuclideanBasis M σ hn).symm := by
  let B := fullLatticeEuclideanBasis M σ hn
  let D := fullLatticeEuclideanBasis (traceDualFullLattice M hn) σ hn
  have H : D.toLinearMap.adjoint.comp B.toLinearMap = LinearMap.id := by
    dsimp [D,B]
    rw [fullLatticeEuclideanBasis_toLinearMap,fullLatticeEuclideanBasis_toLinearMap,
      ← Matrix.toLin_conjTranspose]
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose]
    rw [← Matrix.toLin_mul,traceDual_embeddingMatrix_mul,Matrix.toLin_one]
  have HD : D.toLinearMap.adjoint = B.symm.toLinearMap := by
    ext x : 1
    have J := LinearMap.congr_fun H (B.symm x)
    simpa using J
  have HD' := congrArg LinearMap.adjoint HD
  simp only [LinearMap.adjoint_adjoint] at HD'
  apply ContinuousLinearEquiv.ext
  funext x
  change D.toLinearMap x = B.symm.toContinuousLinearMap.adjoint.toLinearMap x
  rw [← ContinuousLinearMap.adjoint_toLinearMap]
  exact LinearMap.congr_fun HD' x

 

theorem fullLatticeTheta_traceDual (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : finrank ℚ K = n) (t : ℝ) (ht : 0 < t) :
    fullLatticeTheta M σ t = (((|(embeddingMatrix M σ).det⁻¹|:ℝ):ℂ) *
      (Real.pi/(t:ℂ)) ^ ((n:ℂ)/2)) *
      fullLatticeTheta (traceDualFullLattice M hn) σ (Real.pi^2/t) := by
  rw [fullLatticeTheta_inversion M σ hn t ht,fullLatticeTheta_eq _ σ hn,
    traceDualFullLattice_euclideanBasis]

end PrimeDegreePackets


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

def normalizedTheta (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (t : ℝ) : ℂ :=
  latticeTheta B (Real.pi*t)

def normalizedThetaTail (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) : ℝ → ℂ :=
  (Set.Ioi 1).indicator (fun t => thetaRemainder B (Real.pi*max t 1))

lemma normalizedTheta_inversion (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (t : ℝ) (ht : 0 < t) :
    normalizedTheta B t = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (t:ℂ)^(-((Fintype.card d:ℂ)/2)) * normalizedTheta (adjointEquiv B.symm) t⁻¹ := by
  unfold normalizedTheta
  rw [latticeTheta_inversion B (Real.pi*t) (mul_pos Real.pi_pos ht)]
  have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h1 : (Real.pi:ℂ) / ((Real.pi*t:ℝ):ℂ) = (t:ℂ)⁻¹ := by
    rw [Complex.ofReal_mul]; field_simp
  have h2 : Real.pi^2/(Real.pi*t) = Real.pi*t⁻¹ := by field_simp
  rw [h1,h2,Complex.inv_cpow_ofReal_nonneg ht.le,←Complex.cpow_neg]

lemma normalizedThetaTail_locallyIntegrable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    LocallyIntegrable (normalizedThetaTail B) := by
  have hc : Continuous (fun t : ℝ => thetaRemainder B (Real.pi*max t 1)) :=
    (thetaRemainder_continuousOn B).comp_continuous
      (continuous_const.mul (continuous_id.max continuous_const))
      (fun t => mul_pos Real.pi_pos (lt_of_lt_of_le zero_lt_one (le_max_right t 1)))
  exact hc.locallyIntegrable.indicator measurableSet_Ioi

lemma normalizedThetaTail_bigO_exp (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    ∃ a : ℝ, 0 < a ∧ normalizedThetaTail B =O[atTop] (fun t => Real.exp (-a*t)) := by
  obtain ⟨a,C,ha,_,hbound⟩ := thetaRemainder_exponential_bound B
  refine ⟨a*Real.pi,mul_pos ha Real.pi_pos,IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
  have hpt : 1 ≤ Real.pi*t := by nlinarith [Real.pi_gt_three]
  simpa [normalizedThetaTail,ht,max_eq_left ht.le,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),mul_assoc] using hbound (Real.pi*t) hpt

lemma normalizedThetaTail_bigO_zero (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : ℝ) : normalizedThetaTail B =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
  apply IsBigO.of_bound 0
  have H : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
  filter_upwards [H] with t ht
  simp [normalizedThetaTail,not_lt.mpr ht.le]

lemma normalizedThetaTail_mellin_convergent (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (s : ℂ) : MellinConvergent (normalizedThetaTail B) s := by
  obtain ⟨a,ha,hbound⟩ := normalizedThetaTail_bigO_exp B
  exact mellinConvergent_of_isBigO_rpow_exp ha
    ((normalizedThetaTail_locallyIntegrable B).locallyIntegrableOn (Set.Ioi 0)) hbound
    (normalizedThetaTail_bigO_zero B (s.re-1)) (by linarith)

@[fun_prop] lemma normalizedThetaTail_mellin_differentiable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    Differentiable ℂ (mellin (normalizedThetaTail B)) := by
  obtain ⟨a,ha,hbound⟩ := normalizedThetaTail_bigO_exp B
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp ha
    ((normalizedThetaTail_locallyIntegrable B).locallyIntegrableOn (Set.Ioi 0)) hbound
    (normalizedThetaTail_bigO_zero B (s.re-1)) (by linarith)

lemma normalizedThetaTail_eq (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 1 < t) : normalizedThetaTail B t = normalizedTheta B t - 1 := by
  rw [normalizedThetaTail,indicator_of_mem (show t ∈ Set.Ioi 1 from ht),max_eq_left ht.le]
  exact thetaRemainder_eq B (mul_pos Real.pi_pos (zero_lt_one.trans ht))

lemma normalizedTheta_decomposition (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 0 < t) (hne : t ≠ 1) :
    normalizedTheta B t - 1 =
      normalizedThetaTail B t +
        ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) * (t:ℂ)^(-((Fintype.card d:ℂ)/2)) *
          normalizedThetaTail (adjointEquiv B.symm) t⁻¹ +
        ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
          (Set.Ioc 0 1).indicator (fun x : ℝ => (x:ℂ)^(-((Fintype.card d:ℂ)/2))) t -
        (Set.Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ)) t := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr hlt
    rw [normalizedThetaTail_eq _ hinv,
      show normalizedThetaTail B t = 0 by simp [normalizedThetaTail,not_lt.mpr hlt.le],
      indicator_of_mem (show t ∈ Set.Ioc 0 1 from ⟨ht,hlt.le⟩),
      indicator_of_mem (show t ∈ Set.Ioc 0 1 from ⟨ht,hlt.le⟩),normalizedTheta_inversion B t ht]
    ring
  · have hinv : t⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hgt)).mpr hgt
    rw [normalizedThetaTail_eq _ hgt,
      show normalizedThetaTail (adjointEquiv B.symm) t⁻¹ = 0 by
        simp [normalizedThetaTail,not_lt.mpr hinv.le],
      indicator_of_notMem (show t ∉ Set.Ioc 0 1 from fun h => (not_le_of_gt hgt) h.2),
      indicator_of_notMem (show t ∉ Set.Ioc 0 1 from fun h => (not_le_of_gt hgt) h.2)]
    ring

def thetaMellinContinuation (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (s : ℂ) : ℂ :=
  mellin (normalizedThetaTail B) s + ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
    mellin (normalizedThetaTail (adjointEquiv B.symm)) ((Fintype.card d:ℂ)/2-s) +
      ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) / (s-(Fintype.card d:ℂ)/2) - 1/s

 

def thetaMellinXi (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (s : ℂ) : ℂ :=
  s*(s-(Fintype.card d:ℂ)/2) *
    (mellin (normalizedThetaTail B) s + ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      mellin (normalizedThetaTail (adjointEquiv B.symm)) ((Fintype.card d:ℂ)/2-s)) +
    ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ)*s - (s-(Fintype.card d:ℂ)/2)

lemma thetaMellinXi_differentiable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    Differentiable ℂ (thetaMellinXi B) := by
  unfold thetaMellinXi
  fun_prop

lemma thetaMellinXi_eq (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {s : ℂ} (hs : s ≠ 0) (hsa : s ≠ (Fintype.card d:ℂ)/2) :
    thetaMellinXi B s = s*(s-(Fintype.card d:ℂ)/2)*thetaMellinContinuation B s := by
  unfold thetaMellinXi thetaMellinContinuation
  generalize (Fintype.card d:ℂ)/2 = a at hsa ⊢
  field_simp [hs,sub_ne_zero.mpr hsa]

lemma mellinConvergent_inv {f : ℝ → ℂ} {s : ℂ} :
    MellinConvergent (fun t => f t⁻¹) s ↔ MellinConvergent f (-s) := by
  simpa only [Real.rpow_neg_one,Complex.ofReal_neg,Complex.ofReal_one,div_neg,_root_.div_one] using (MellinConvergent.comp_rpow (f := f) (s := s) (a := -1) (by norm_num))

 

theorem normalizedTheta_hasMellin (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {s : ℂ} (hs : (Fintype.card d:ℝ)/2 < s.re) :
    HasMellin (fun t => normalizedTheta B t - 1) s (thetaMellinContinuation B s) := by
  let a : ℂ := (Fintype.card d:ℂ)/2
  let c : ℂ := ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ)
  let P := normalizedThetaTail B
  let Q := normalizedThetaTail (adjointEquiv B.symm)
  let R := (Set.Ioc 0 1).indicator (fun t : ℝ => (t:ℂ)^(-a))
  let J := (Set.Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ))
  let q := fun t : ℝ => c • ((t:ℂ)^(-a) • Q t⁻¹)
  have ha : a.re = (Fintype.card d:ℝ)/2 := by simp [a]
  have has : 0 < s.re + (-a).re := by rw [Complex.neg_re,ha]; linarith
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  have hP : MellinConvergent P s := normalizedThetaTail_mellin_convergent B s
  have hQ : MellinConvergent (fun t => (t:ℂ)^(-a) • Q t⁻¹) s := by
    apply MellinConvergent.cpow_smul.mpr
    apply mellinConvergent_inv.mpr
    exact normalizedThetaTail_mellin_convergent _ _
  have hq : MellinConvergent q s := hQ.const_smul c
  have hR : HasMellin R s (1/(s-a)) := by
    simpa only [sub_eq_add_neg] using hasMellin_cpow_Ioc (-a) has
  have hJ : HasMellin J s (1/s) := hasMellin_one_Ioc hs0
  have hPR := hasMellin_add hP hq
  have hPRR := hasMellin_add hPR.1 (hR.1.const_smul c)
  have HF := hasMellin_sub hPRR.1 hJ.1
  have hqeq : mellin q s = c * mellin Q (a-s) := by
    calc
      mellin q s = c • mellin (fun t => (t:ℂ)^(-a) • Q t⁻¹) s :=
        mellin_const_smul _ s c
      _ = c * mellin Q (a-s) := by
        rw [mellin_cpow_smul,mellin_comp_inv,smul_eq_mul]
        congr 2
        ring
  have HFval : mellin (fun t => (P t + q t) + c • R t - J t) s =
      thetaMellinContinuation B s := by
    rw [HF.2,hPRR.2,hPR.2,hqeq,mellin_const_smul,hR.2,hJ.2,smul_eq_mul]
    simp only [thetaMellinContinuation,P,Q,c,a,mul_one_div]
  have Hne : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi 0)), t ≠ 1 := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp
  have HE : (fun t => normalizedTheta B t - 1) =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t => (P t + q t) + c • R t - J t) := by
    filter_upwards [Hne,ae_restrict_mem measurableSet_Ioi] with t hne ht
    simpa only [P,q,c,a,R,J,smul_eq_mul,mul_assoc] using
      normalizedTheta_decomposition B ht hne
  have HI : (fun t : ℝ => (t:ℂ)^(s-1) • (normalizedTheta B t-1))
      =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t : ℝ => (t:ℂ)^(s-1) • ((P t+q t)+c • R t-J t)) := by
    filter_upwards [HE] with t ht
    rw [ht]
  refine ⟨HF.1.congr HI.symm, ?_⟩
  exact (integral_congr_ae HI).trans HFval

lemma thetaDual_involutive (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    adjointEquiv (adjointEquiv B.symm).symm = B := by
  apply ContinuousLinearEquiv.ext
  funext x
  change B.toContinuousLinearMap.adjoint.adjoint x = B x
  rw [ContinuousLinearMap.adjoint_adjoint]
  rfl

lemma adjointEquiv_det (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    LinearMap.det (adjointEquiv B).toLinearMap = LinearMap.det B.toLinearMap := by
  classical
  change LinearMap.det B.toContinuousLinearMap.adjoint.toLinearMap = _
  rw [← ContinuousLinearMap.adjoint_toLinearMap,
    ← LinearMap.det_toMatrix (EuclideanSpace.basisFun d ℝ).toBasis,
    LinearMap.toMatrix_adjoint]
  simp only [Matrix.det_conjTranspose,star_trivial,LinearMap.det_toMatrix]
  rfl

lemma thetaDual_det (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    LinearMap.det (adjointEquiv B.symm).toLinearMap = (LinearMap.det B.toLinearMap)⁻¹ := by
  rw [adjointEquiv_det]
  exact B.toLinearEquiv.det_coe_symm

 

theorem thetaMellinXi_functional_equation (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (s : ℂ) : thetaMellinXi B s = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      thetaMellinXi (adjointEquiv B.symm) ((Fintype.card d:ℂ)/2-s) := by
  have hdet : LinearMap.det B.toLinearMap ≠ 0 := B.toLinearEquiv.isUnit_det'.ne_zero
  have hd : ((|(LinearMap.det (adjointEquiv B.symm).toLinearMap)⁻¹|:ℝ):ℂ) =
      (((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ))⁻¹ := by
    rw [thetaDual_det]
    simp
  have hc : ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) ≠ 0 := by
    simpa only [ne_eq,Complex.ofReal_eq_zero,abs_eq_zero,inv_eq_zero] using hdet
  unfold thetaMellinXi
  rw [thetaDual_involutive,hd]
  generalize (Fintype.card d:ℂ)/2 = a
  simp only [sub_sub_cancel]
  generalize ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) = c at hc ⊢
  field_simp [hc]
  ring

end PrimeDegreePackets.ThetaConstruction

open Module MeasureTheory
namespace PrimeDegreePackets
open ThetaConstruction
variable {n : ℕ} {K : Type*} [Field K] [NumberField K]

 

def fullLatticeThetaXi (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : finrank ℚ K = n) : ℂ → ℂ := thetaMellinXi (fullLatticeEuclideanBasis M σ hn)

theorem fullLatticeThetaXi_differentiable (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : finrank ℚ K = n) : Differentiable ℂ (fullLatticeThetaXi M σ hn) :=
  thetaMellinXi_differentiable _

theorem fullLatticeThetaXi_functional_equation (M : FullLattice n K)
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n) (s : ℂ) :
    fullLatticeThetaXi M σ hn s = ((|(embeddingMatrix M σ).det⁻¹|:ℝ):ℂ) *
      fullLatticeThetaXi (traceDualFullLattice M hn) σ hn ((n:ℂ)/2-s) := by
  unfold fullLatticeThetaXi
  rw [thetaMellinXi_functional_equation,fullLatticeEuclideanBasis_det,
    traceDualFullLattice_euclideanBasis]
  simp

theorem fullLatticeTheta_hasMellin (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : finrank ℚ K = n) {s : ℂ} (hs : (n:ℝ)/2 < s.re) :
    HasMellin (fun t => fullLatticeTheta M σ (Real.pi*t) - 1) s
      (thetaMellinContinuation (fullLatticeEuclideanBasis M σ hn) s) := by
  simpa only [normalizedTheta,←fullLatticeTheta_eq M σ hn] using
    (normalizedTheta_hasMellin (fullLatticeEuclideanBasis M σ hn) (by simpa using hs))

end PrimeDegreePackets


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma gaussian_hasMellin {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun t : ℝ => (Real.exp (-a*t):ℂ)) s ((a:ℂ)^(-s)*Complex.Gamma s) := by
  have HI : MellinConvergent (fun t : ℝ => (Real.exp (-t):ℂ)) s := by
    simpa only [MellinConvergent,smul_eq_mul,mul_comm] using Complex.GammaIntegral_convergent hs
  have HE : (fun t : ℝ => (Real.exp (-a*t):ℂ)) =
      (fun t : ℝ => (Real.exp (-(a*t)):ℂ)) := by funext t; rw [neg_mul]
  rw [HE]
  refine ⟨(MellinConvergent.comp_mul_left ha).mpr HI, ?_⟩
  rw [mellin_comp_mul_left (fun t : ℝ => (Real.exp (-t):ℂ)) s ha,←Complex.GammaIntegral_eq_mellin,
    ←Complex.Gamma_eq_integral hs,smul_eq_mul]

def latticeEnergy (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (z : NonzeroIntegerVector d) : ℝ := Real.pi * ‖B (euclideanInteger z.1)‖^2

lemma latticeEnergy_pos (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (z : NonzeroIntegerVector d) : 0 < latticeEnergy B z := by
  obtain ⟨c,hc,hbound⟩ := theta_lattice_lower_bound B
  exact mul_pos Real.pi_pos (sq_pos_of_pos (hc.trans_le (hbound z)))

lemma thetaRemainder_eq_real_sum (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (_ht : 0 < t) : thetaRemainder B (Real.pi*t) =
      ((∑' z : NonzeroIntegerVector d, Real.exp (-latticeEnergy B z*t)):ℝ) := by
  unfold thetaRemainder
  rw [Complex.ofReal_tsum]
  congr 1
  funext z
  rw [Complex.ofReal_exp]
  congr 1
  simp only [latticeEnergy,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_pow]
  ring

lemma realGaussian_summable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun z : NonzeroIntegerVector d => Real.exp (-latticeEnergy B z*t)) := by
  have H := (thetaRemainder_summable B (mul_pos Real.pi_pos ht)).norm
  convert H using 1
  funext z
  rw [gaussianTerm_norm]
  congr 1
  simp only [latticeEnergy]
  ring

 

def latticeEpsteinSeries (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (s : ℂ) : ℂ :=
  ∑' z : NonzeroIntegerVector d, (latticeEnergy B z:ℂ)^(-s)

lemma mellinGaussian_norm_sum (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ∑' z : NonzeroIntegerVector d, ‖(t:ℂ)^(s-1) * (Real.exp (-latticeEnergy B z*t):ℂ)‖ =
      ‖(t:ℂ)^((s.re:ℂ)-1) * (normalizedTheta B t-1)‖ := by
  have hp : ∀ z : NonzeroIntegerVector d, 0 ≤ Real.exp (-latticeEnergy B z*t) :=
    fun z => (Real.exp_pos _).le
  unfold normalizedTheta
  rw [←thetaRemainder_eq B (mul_pos Real.pi_pos ht),thetaRemainder_eq_real_sum B ht]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg hp)]
  simp_rw [abs_of_pos (Real.exp_pos _)]
  rw [tsum_mul_left]
  congr 1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

 

theorem thetaMellinContinuation_hasSum_epstein (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {s : ℂ} (hs : (Fintype.card d:ℝ)/2 < s.re) :
    HasSum (fun z : NonzeroIntegerVector d => (latticeEnergy B z:ℂ)^(-s) * Complex.Gamma s)
      (thetaMellinContinuation B s) := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  let F := fun (z : NonzeroIntegerVector d) (t : ℝ) =>
    (t:ℂ)^(s-1) * (Real.exp (-latticeEnergy B z*t):ℂ)
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  have HI (z : NonzeroIntegerVector d) : Integrable (F z) μ :=
    (gaussian_hasMellin (latticeEnergy_pos B z) hs0).1
  have Hsum (t : ℝ) (ht : 0 < t) : Summable (fun z : NonzeroIntegerVector d => ‖F z t‖) := by
    simpa only [F,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      (realGaussian_summable B ht).mul_left ‖(t:ℂ)^(s-1)‖
  have HE : (fun t => ∑' z : NonzeroIntegerVector d, ‖F z t‖ₑ) =ᵐ[μ]
      (fun t => ‖(t:ℂ)^((s.re:ℂ)-1) * (normalizedTheta B t-1)‖ₑ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp_rw [←ofReal_norm]
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun z => norm_nonneg (F z t)) (Hsum t ht)]
    congr 1
    exact mellinGaussian_norm_sum B s ht
  have Hreal : Integrable (fun t : ℝ => (t:ℂ)^((s.re:ℂ)-1) * (normalizedTheta B t-1)) μ :=
    (normalizedTheta_hasMellin B (by simpa using hs)).1
  have Hfinite : ∑' z : NonzeroIntegerVector d, ∫⁻ t, ‖F z t‖ₑ ∂μ ≠ ∞ := by
    rw [←lintegral_tsum (fun z => (HI z).aestronglyMeasurable.enorm),lintegral_congr_ae HE]
    exact (hasFiniteIntegral_iff_enorm.mp Hreal.hasFiniteIntegral).ne
  have HT := integral_tsum (fun z => (HI z).aestronglyMeasurable) Hfinite
  have HFeq : (fun t => ∑' z : NonzeroIntegerVector d, F z t) =ᵐ[μ]
      (fun t => (t:ℂ)^(s-1) * (normalizedTheta B t-1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp [F]
    rw [tsum_mul_left,←Complex.ofReal_tsum,←thetaRemainder_eq_real_sum B ht,
      thetaRemainder_eq B (mul_pos Real.pi_pos ht)]
    rfl
  have HFi (z : NonzeroIntegerVector d) : ∫ t, F z t ∂μ =
      (latticeEnergy B z:ℂ)^(-s) * Complex.Gamma s :=
    (gaussian_hasMellin (latticeEnergy_pos B z) hs0).2
  have Hfinite' : ∑' z : NonzeroIntegerVector d, ‖∫ t, F z t ∂μ‖ₑ ≠ ∞ := by
    apply _root_.ne_of_lt
    exact (ENNReal.tsum_le_tsum (fun z => enorm_integral_le_lintegral_enorm (F z))).trans_lt
      (lt_top_iff_ne_top.mpr Hfinite)
  have HsumInt : Summable (fun z : NonzeroIntegerVector d => ∫ t, F z t ∂μ) :=
    (tsum_enorm_ne_top_iff_summable_norm.mp Hfinite').of_norm
  have HV : (∑' z : NonzeroIntegerVector d, ∫ t, F z t ∂μ) = thetaMellinContinuation B s := by
    rw [←HT,integral_congr_ae HFeq]
    exact (normalizedTheta_hasMellin B hs).2
  have HHas : HasSum (fun z : NonzeroIntegerVector d => ∫ t, F z t ∂μ)
      (thetaMellinContinuation B s) := HV ▸ HsumInt.hasSum
  simpa only [HFi] using HHas

lemma latticeEpsteinSeries_summable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {s : ℂ} (hs : (Fintype.card d:ℝ)/2 < s.re) :
    Summable (fun z : NonzeroIntegerVector d => (latticeEnergy B z:ℂ)^(-s)) := by
  have hg : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos
    (lt_of_le_of_lt (by positivity) hs)
  have H := (thetaMellinContinuation_hasSum_epstein B hs).summable.div_const (Complex.Gamma s)
  simpa only [mul_div_cancel_right₀ _ hg] using H

theorem thetaMellinContinuation_eq_epstein (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {s : ℂ} (hs : (Fintype.card d:ℝ)/2 < s.re) :
    thetaMellinContinuation B s = Complex.Gamma s * latticeEpsteinSeries B s := by
  rw [←(thetaMellinContinuation_hasSum_epstein B hs).tsum_eq,tsum_mul_right,mul_comm]
  rfl

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
