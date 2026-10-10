import Mathlib
import OAI.NumberTheory.PrimePackets.IdealClasses

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
open scoped BigOperators Classical ArithmeticFunction.Moebius
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
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]
local instance congruenceLatticesDecidableEq : DecidableEq d := Classical.decEq d

 
def integerCongruenceEquiv (N : ℕ) [NeZero N] :
    (d → ℤ) ≃ (d → Fin N) × (d → ℤ) where
  toFun z := (fun i => (Int.divModEquiv N (z i)).2,
    fun i => (Int.divModEquiv N (z i)).1)
  invFun rq i := (Int.divModEquiv N).symm (rq.2 i, rq.1 i)
  left_inv z := by
    funext i
    exact (Int.divModEquiv N).symm_apply_apply (z i)
  right_inv rq := by
    apply Prod.ext <;> funext i
    · exact congrArg Prod.snd ((Int.divModEquiv N).apply_symm_apply (rq.2 i, rq.1 i))
    · exact congrArg Prod.fst ((Int.divModEquiv N).apply_symm_apply (rq.2 i, rq.1 i))

 
def congruencePoint (N : ℕ) (r : d → Fin N) : d → ℝ :=
  fun i => (r i : ℝ) / N

omit [Fintype d] in
lemma scaledInteger_congruence (N : ℕ) [NeZero N]
    (r : d → Fin N) (q : d → ℤ) :
    (N : ℝ)⁻¹ • euclideanInteger ((integerCongruenceEquiv N).symm (r,q)) =
      toLp 2 (congruencePoint N r) + euclideanInteger q := by
  ext i
  simp only [integerCongruenceEquiv, Equiv.coe_fn_symm_mk, Int.divModEquiv_symm_apply,
    euclideanInteger, integerVector, congruencePoint, PiLp.smul_apply, PiLp.add_apply,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, smul_eq_mul]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp
  ring

omit [Fintype d] in
lemma scaledInteger_congruence_pair (N : ℕ) [NeZero N]
    (rq : (d → Fin N) × (d → ℤ)) :
    (N : ℝ)⁻¹ • euclideanInteger ((integerCongruenceEquiv N).symm rq) =
      toLp 2 (congruencePoint N rq.1) + euclideanInteger rq.2 :=
  scaledInteger_congruence N rq.1 rq.2

 

def periodicLatticeTheta (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (b : ℝ) : ℂ :=
  ∑' z : d → ℤ, w ((integerCongruenceEquiv N z).1) *
    Complex.exp (-(b:ℂ) * ‖B ((N:ℝ)⁻¹ • euclideanInteger z)‖^2)

lemma congruenceProduct_summable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (b : ℝ) (hb : 0 < b) :
    Summable (fun rq : (d → Fin N) × (d → ℤ) => w rq.1 *
      Complex.exp (-(b:ℂ) * ‖B (toLp 2 (congruencePoint N rq.1) +
        euclideanInteger rq.2)‖^2)) := by
  classical
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
  exact ⟨fun r => ((cosetLatticeTheta_summable B (congruencePoint N r) b hb).mul_left
    (w r)).norm, Summable.of_finite⟩

lemma periodicLatticeTheta_summable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (b : ℝ) (hb : 0 < b) :
    Summable (fun z : d → ℤ => w ((integerCongruenceEquiv N z).1) *
      Complex.exp (-(b:ℂ) * ‖B ((N:ℝ)⁻¹ • euclideanInteger z)‖^2)) := by
  apply (integerCongruenceEquiv N).symm.summable_iff.mp
  simpa only [Function.comp_def, Equiv.apply_symm_apply, scaledInteger_congruence_pair] using
    congruenceProduct_summable B N w b hb

 
theorem periodicLatticeTheta_eq_congruenceTheta
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (b : ℝ) (hb : 0 < b) :
    periodicLatticeTheta B N w b = congruenceTheta B (congruencePoint N) w b := by
  classical
  unfold periodicLatticeTheta
  rw [← (integerCongruenceEquiv N).symm.tsum_eq]
  simp only [Equiv.apply_symm_apply, scaledInteger_congruence_pair]
  rw [(congruenceProduct_summable B N w b hb).tsum_prod, tsum_fintype]
  simp only [congruenceTheta, cosetLatticeTheta, tsum_mul_left]

 

theorem periodicLatticeTheta_poisson
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (b : ℝ) (hb : 0 < b) :
    periodicLatticeTheta B N w b = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        ∑' m : d → ℤ, Complex.exp (-((Real.pi^2/b:ℝ):ℂ) *
          ‖adjointEquiv B.symm (euclideanInteger m)‖^2) *
          congruenceThetaFourierWeight (congruencePoint N) w m := by
  rw [periodicLatticeTheta_eq_congruenceTheta B N w b hb]
  exact congruenceTheta_poisson B (congruencePoint N) w b hb

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma thetaRemainder_eq_ofReal (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (t : ℝ) : thetaRemainder B t =
      ((∑' z : NonzeroIntegerVector d, Real.exp (-t*‖B (euclideanInteger z.1)‖^2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro z
  simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]

lemma thetaRemainder_sum_norm (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (t : ℝ) :
    (∑' z : NonzeroIntegerVector d,
      ‖Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z.1)‖^2)‖) = ‖thetaRemainder B t‖ := by
  rw [thetaRemainder_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (fun _ => (Real.exp_pos _).le))]
  apply tsum_congr
  intro z
  exact gaussianTerm_norm _ _

 
def weightedThetaRemainder
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (t : ℝ) : ℂ :=
  ∑' z : NonzeroIntegerVector d,
    a z.1 * Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z.1)‖^2)

lemma weightedThetaRemainder_summable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M)
    {t : ℝ} (ht : 0 < t) : Summable (fun z : NonzeroIntegerVector d =>
      a z.1 * Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z.1)‖^2)) := by
  apply Summable.of_norm_bounded ((thetaRemainder_summable B ht).norm.mul_left M)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ha z.1) (norm_nonneg _)

lemma weightedThetaRemainder_bound
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M)
    {t : ℝ} (ht : 0 < t) :
    ‖weightedThetaRemainder B a t‖ ≤ M * ‖thetaRemainder B t‖ := by
  calc
    _ ≤ ∑' z : NonzeroIntegerVector d,
        ‖a z.1 * Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z.1)‖^2)‖ :=
      norm_tsum_le_tsum_norm (weightedThetaRemainder_summable B a M ha ht).norm
    _ ≤ ∑' z : NonzeroIntegerVector d,
        M * ‖Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z.1)‖^2)‖ := by
      apply (weightedThetaRemainder_summable B a M ha ht).norm.tsum_le_tsum _
        ((thetaRemainder_summable B ht).norm.mul_left M)
      intro z
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (ha z.1) (norm_nonneg _)
    _ = _ := by rw [tsum_mul_left, thetaRemainder_sum_norm]

lemma weightedThetaRemainder_continuousOn
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M) :
    ContinuousOn (weightedThetaRemainder B a) (Set.Ioi 0) := by
  have hM : 0 ≤ M := (norm_nonneg (a 0)).trans (ha 0)
  intro t ht
  change 0 < t at ht
  have hc : ContinuousOn (weightedThetaRemainder B a) (Set.Ioi (t/2)) := by
    apply continuousOn_tsum (u := fun z : NonzeroIntegerVector d =>
      M * ‖Complex.exp (-((t/2:ℝ):ℂ) * ‖B (euclideanInteger z.1)‖^2)‖)
    · intro z; fun_prop
    · exact (thetaRemainder_summable B (by linarith)).norm.mul_left M
    · intro z x hx
      change t/2 < x at hx
      rw [norm_mul]
      apply mul_le_mul (ha z.1) _ (norm_nonneg _) hM
      rw [gaussianTerm_norm, gaussianTerm_norm]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg ‖B (euclideanInteger z.1)‖]
  exact (hc.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

lemma weightedThetaRemainder_uniform_exponential_bound (R M : ℝ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d),
        ‖B.symm.toContinuousLinearMap‖ ≤ R →
        ∀ a : (d → ℤ) → ℂ, (∀ z, ‖a z‖ ≤ M) →
        ∀ t : ℝ, 1 ≤ t → ‖weightedThetaRemainder B a t‖ ≤ C * Real.exp (-c*t) := by
  obtain ⟨c,C,hc,hC,hbound⟩ := thetaRemainder_uniform_exponential_bound (d := d) R hR
  refine ⟨c,M*C,hc,mul_nonneg hM hC,fun B hB a ha t ht => ?_⟩
  calc
    _ ≤ M * ‖thetaRemainder B t‖ := weightedThetaRemainder_bound B a M ha (by linarith)
    _ ≤ M * (C * Real.exp (-c*t)) := mul_le_mul_of_nonneg_left (hbound B hB t ht) hM
    _ = _ := by ring

 

def weightedThetaTail (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) : ℝ → ℂ :=
  (Set.Ioi 1).indicator (fun t => weightedThetaRemainder B a (max t 1))

lemma weightedThetaTail_locallyIntegrable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M) :
    LocallyIntegrable (weightedThetaTail B a) := by
  have hc : Continuous (fun t : ℝ => weightedThetaRemainder B a (max t 1)) :=
    (weightedThetaRemainder_continuousOn B a M ha).comp_continuous
      (continuous_id.max continuous_const) (fun t => lt_of_lt_of_le zero_lt_one (le_max_right t 1))
  exact hc.locallyIntegrable.indicator measurableSet_Ioi

lemma weightedThetaTail_bigO_exp
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M) :
    ∃ c : ℝ, 0 < c ∧ weightedThetaTail B a =O[atTop] (fun t => Real.exp (-c*t)) := by
  obtain ⟨c,C,hc,_,hbound⟩ := weightedThetaRemainder_uniform_exponential_bound (d := d)
    ‖B.symm.toContinuousLinearMap‖ M (norm_nonneg _) ((norm_nonneg (a 0)).trans (ha 0))
  refine ⟨c,hc,IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
  simpa [weightedThetaTail,ht,max_eq_left ht.le,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
    hbound B le_rfl a ha t ht.le

 

theorem weightedThetaTail_mellin_differentiable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M) :
    Differentiable ℂ (mellin (weightedThetaTail B a)) := by
  obtain ⟨c,hc,hbound⟩ := weightedThetaTail_bigO_exp B a M ha
  intro s
  apply mellin_differentiableAt_of_isBigO_rpow_exp hc
    ((weightedThetaTail_locallyIntegrable B a M ha).locallyIntegrableOn (Set.Ioi 0))
    hbound (b := s.re-1) _ (by linarith)
  apply IsBigO.of_bound 0
  have H : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
  filter_upwards [H] with t ht
  simp [weightedThetaTail,not_lt.mpr ht.le]

lemma congruenceThetaFourierWeight_bound {I : Type*} [Fintype I]
    (x : I → d → ℝ) (w : I → ℂ) (m : d → ℤ) :
    ‖congruenceThetaFourierWeight x w m‖ ≤ ∑ i, ‖w i‖ := by
  calc
    _ ≤ ∑ i, ‖w i * UnitAddTorus.mFourier m (torusProjection (x i))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, cosetPhase_norm, mul_one]

 

theorem congruenceDualTail_entire {I : Type*} [Fintype I]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : I → d → ℝ) (w : I → ℂ) :
    Differentiable ℂ (mellin
      (weightedThetaTail (adjointEquiv B.symm) (congruenceThetaFourierWeight x w))) :=
  weightedThetaTail_mellin_differentiable _ _ (∑ i, ‖w i‖)
    (congruenceThetaFourierWeight_bound x w)

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]
local instance congruenceLatticesGaussianDecidableEq : DecidableEq d := Classical.decEq d

lemma weightedLatticeGaussian_summable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M)
    {t : ℝ} (ht : 0 < t) : Summable (fun z : d → ℤ =>
      a z * Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z)‖^2)) := by
  apply Summable.of_norm_bounded ((latticeTheta_summable B t ht).norm.mul_left M)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ha z) (norm_nonneg _)

lemma weightedLatticeGaussian_decomposition
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M)
    {t : ℝ} (ht : 0 < t) :
    (∑' z : d → ℤ, a z * Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z)‖^2)) =
      a 0 + weightedThetaRemainder B a t := by
  classical
  let f := fun z : d → ℤ => a z * Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z)‖^2)
  have H := (weightedLatticeGaussian_summable B a M ha ht).tsum_eq_add_tsum_ite 0
  have Hz : euclideanInteger (0 : d → ℤ) = 0 := by ext i; simp [euclideanInteger,integerVector]
  have H0 : f 0 = a 0 := by simp [f, Hz]
  change (∑' z, f z) = f 0 + ∑' z, if z = 0 then 0 else f z at H
  rw [H0] at H
  have HE : weightedThetaRemainder B a t = ∑' z, if z = 0 then 0 else f z := by
    change (∑' z : {z : d → ℤ | z ≠ 0}, f z.1) = _
    rw [tsum_subtype {z : d → ℤ | z ≠ 0} f]
    apply tsum_congr
    intro z
    by_cases hz : z = 0 <;> simp [hz,f]
  rw [HE]
  exact H

 

theorem congruenceTheta_poisson_zero_mode {I : Type*} [Fintype I]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : I → d → ℝ) (w : I → ℂ) (b : ℝ) (hb : 0 < b) :
    congruenceTheta B x w b = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        ((∑ i, w i) + weightedThetaRemainder (adjointEquiv B.symm)
          (congruenceThetaFourierWeight x w) (Real.pi^2/b)) := by
  rw [congruenceTheta_poisson B x w b hb]
  have ht : 0 < Real.pi^2/b := div_pos (sq_pos_of_pos Real.pi_pos) hb
  congr 1
  rw [← congruenceThetaFourierWeight_zero x w,
    ← weightedLatticeGaussian_decomposition _ _ (∑ i, ‖w i‖)
      (congruenceThetaFourierWeight_bound x w) ht]
  apply tsum_congr
  intro z
  exact mul_comm _ _

 

theorem congruenceTheta_poisson_of_sum_zero {I : Type*} [Fintype I]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : I → d → ℝ) (w : I → ℂ) (hw : ∑ i, w i = 0)
    (b : ℝ) (hb : 0 < b) :
    congruenceTheta B x w b = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        weightedThetaRemainder (adjointEquiv B.symm)
          (congruenceThetaFourierWeight x w) (Real.pi^2/b) := by
  rw [congruenceTheta_poisson_zero_mode B x w b hb, hw, zero_add]

lemma congruenceWeight_bound (N : ℕ) (w : (d → Fin N) → ℂ) (r : d → Fin N) :
    ‖w r‖ ≤ ∑ j, ‖w j‖ :=
  Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ r)

lemma scaledInteger_gaussian_exponent
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (b : ℝ) (z : d → ℤ) :
    -(b:ℂ) * ‖B ((N:ℝ)⁻¹ • euclideanInteger z)‖^2 =
      -((b/(N:ℝ)^2:ℝ):ℂ) * ‖B (euclideanInteger z)‖^2 := by
  have hN : 0 < (N:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN)]
  push_cast
  ring

 

theorem periodicLatticeTheta_zero_mode
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (b : ℝ) (hb : 0 < b) :
    periodicLatticeTheta B N w b =
      w ((integerCongruenceEquiv N (0 : d → ℤ)).1) +
        weightedThetaRemainder B (fun z => w ((integerCongruenceEquiv N z).1))
          (b / (N:ℝ)^2) := by
  unfold periodicLatticeTheta
  simp_rw [scaledInteger_gaussian_exponent]
  apply weightedLatticeGaussian_decomposition B _ (∑ i, ‖w i‖)
    (fun z => congruenceWeight_bound N w _)
  exact div_pos hb (sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))))

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 
def scaledWeightedThetaTail (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (k : ℝ) : ℝ → ℂ :=
  (Set.Ioi 1).indicator (fun t => weightedThetaRemainder B a (k * max t 1))

lemma scaledWeightedThetaTail_locallyIntegrable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M)
    (k : ℝ) (hk : 0 < k) : LocallyIntegrable (scaledWeightedThetaTail B a k) := by
  have hc : Continuous (fun t : ℝ => weightedThetaRemainder B a (k * max t 1)) :=
    (weightedThetaRemainder_continuousOn B a M ha).comp_continuous
      (continuous_const.mul (continuous_id.max continuous_const))
      (fun t => mul_pos hk (lt_of_lt_of_le zero_lt_one (le_max_right t 1)))
  exact hc.locallyIntegrable.indicator measurableSet_Ioi

lemma scaledWeightedThetaTail_bigO_exp
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M)
    (k : ℝ) (hk : 0 < k) :
    ∃ c : ℝ, 0 < c ∧ scaledWeightedThetaTail B a k =O[atTop] (fun t => Real.exp (-c*t)) := by
  obtain ⟨c,C,hc,_,hbound⟩ := weightedThetaRemainder_uniform_exponential_bound (d := d)
    ‖B.symm.toContinuousLinearMap‖ M (norm_nonneg _) ((norm_nonneg (a 0)).trans (ha 0))
  refine ⟨c*k,mul_pos hc hk,IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_ge_atTop (1/k)] with t ht hkt
  have hkt' : 1 ≤ k*t := by
    have := (div_le_iff₀ hk).mp hkt
    simpa only [mul_comm] using this
  simpa [scaledWeightedThetaTail,ht,max_eq_left ht.le,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),mul_assoc] using hbound B le_rfl a ha (k*t) hkt'

lemma scaledWeightedThetaTail_bigO_zero
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (k b : ℝ) :
    scaledWeightedThetaTail B a k =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
  apply IsBigO.of_bound 0
  have H : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
  filter_upwards [H] with t ht
  simp [scaledWeightedThetaTail,not_lt.mpr ht.le]

lemma scaledWeightedThetaTail_mellin_convergent
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M)
    (k : ℝ) (hk : 0 < k) (s : ℂ) :
    MellinConvergent (scaledWeightedThetaTail B a k) s := by
  obtain ⟨c,hc,hbound⟩ := scaledWeightedThetaTail_bigO_exp B a M ha k hk
  exact mellinConvergent_of_isBigO_rpow_exp hc
    ((scaledWeightedThetaTail_locallyIntegrable B a M ha k hk).locallyIntegrableOn (Set.Ioi 0))
    hbound (scaledWeightedThetaTail_bigO_zero B a k (s.re-1)) (by linarith)

@[fun_prop] theorem scaledWeightedThetaTail_mellin_entire
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M)
    (k : ℝ) (hk : 0 < k) :
    Differentiable ℂ (mellin (scaledWeightedThetaTail B a k)) := by
  obtain ⟨c,hc,hbound⟩ := scaledWeightedThetaTail_bigO_exp B a M ha k hk
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp hc
    ((scaledWeightedThetaTail_locallyIntegrable B a M ha k hk).locallyIntegrableOn (Set.Ioi 0))
    hbound (scaledWeightedThetaTail_bigO_zero B a k (s.re-1)) (by linarith)

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
