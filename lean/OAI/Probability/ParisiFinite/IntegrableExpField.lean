import Mathlib
import OAI.Probability.ParisiFinite.RestrictCode
import OAI.Probability.ParisiFinite.ScalarPhase

namespace OAI

/-! Integrable Exp Field. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set MeasurableSpace
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

omit [Fintype ι] [Nonempty ι] in
lemma integrable_exp_field (A : ι → κ → ℝ) (a : ℝ) (s : ι) :
    Integrable (fun z => Real.exp (a*field A z s)) (gaussianLaw κ) := by
  have h := GaussianFourier.integrable_real_exp_dot (fun k => a*A s k)
  simpa only [GaussianFourier.dot,GaussianFourier.law,gaussianLaw,field,Finset.mul_sum,mul_assoc] using h

omit [Fintype ι] [Nonempty ι] in
lemma integral_exp_field (A : ι → κ → ℝ) (a : ℝ) (s : ι) :
    (∫ z,Real.exp (a*field A z s) ∂gaussianLaw κ)=Real.exp (a^2*kernel A s s/2) := by
  have h := GaussianFourier.integral_real_exp_dot (fun k => a*A s k)
  convert h using 1
  · congr 1
    ext z
    simp only [GaussianFourier.dot,field,Finset.mul_sum,mul_assoc]
  · congr 1
    simp only [kernel,Finset.mul_sum,Finset.sum_div,pow_two]
    apply Finset.sum_congr rfl
    intro k _
    ring

 
def gaussianLogAverage (x : ι → ℝ) (A : ι → κ → ℝ) : ℝ :=
  ∫ z,Real.log (average x (fun s => Real.exp (field A z s))) ∂gaussianLaw κ

lemma integrable_gaussianLogAverage (x : ι → ℝ) (A : ι → κ → ℝ) :
    Integrable (fun z => Real.log (average x (fun s => Real.exp (field A z s)))) (gaussianLaw κ) := by
  simp_rw [log_average_exp]
  exact (integrable_logPartition (fun s => (integrable_const (x s)).add (integrable_field A s))).sub (integrable_const _)

omit [Fintype ι] [Nonempty ι] in
lemma empirical_log_exp {r : ℕ} (hr : 0<r) (f : ι → ℝ) (σ : Fin r → ι) :
    Real.log (empiricalMean (fun s => Real.exp (f s)) σ)=logPartition (fun i => f (σ i))-Real.log (r:ℝ) := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  change Real.log (partition (fun i => f (σ i))/(r:ℝ))=_
  rw [Real.log_div (partition_pos (fun i => f (σ i))).ne' (Nat.cast_ne_zero.mpr hr.ne')]
  rfl

omit [Fintype ι] [Nonempty ι] in
lemma integrable_empirical_log_exp {r : ℕ} (hr : 0<r) (A : ι → κ → ℝ) (σ : Fin r → ι) :
    Integrable (fun z => Real.log (empiricalMean (fun s => Real.exp (field A z s)) σ)) (gaussianLaw κ) := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  simp_rw [empirical_log_exp hr]
  exact (integrable_logPartition (fun i => integrable_field A (σ i))).sub (integrable_const _)

def samplePressure {r : ℕ} (A : ι → κ → ℝ) (σ : Fin r → ι) : ℝ :=
  expected (fun i => A (σ i))-Real.log (r:ℝ)

omit [Fintype ι] [Nonempty ι] in
lemma integral_empirical_log_exp {r : ℕ} (hr : 0<r) (A : ι → κ → ℝ) (σ : Fin r → ι) :
    (∫ z,Real.log (empiricalMean (fun s => Real.exp (field A z s)) σ) ∂gaussianLaw κ)=samplePressure A σ := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  simp_rw [empirical_log_exp hr]
  rw [integral_sub (integrable_logPartition (fun i => integrable_field A (σ i))) (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]
  rfl

omit [Nonempty ι] in
lemma integrable_average_exp_field (x : ι → ℝ) (A : ι → κ → ℝ) (a : ℝ) :
    Integrable (fun z => average x (fun s => Real.exp (a*field A z s))) (gaussianLaw κ) :=
  integrable_finsetSum _ (fun s _ => (integrable_exp_field A a s).const_mul _)

lemma integral_average_exp_field_le (x : ι → ℝ) (A : ι → κ → ℝ) {M : ℝ}
    (hM : ∀ s,kernel A s s≤M) (a : ℝ) :
    (∫ z,average x (fun s => Real.exp (a*field A z s)) ∂gaussianLaw κ)≤Real.exp (a^2*M/2) := by
  simp only [average]
  rw [integral_finsetSum _ (fun s _ => (integrable_exp_field A a s).const_mul _)]
  simp only [integral_const_mul,integral_exp_field]
  calc
    _ ≤ ∑ s,weight x s*Real.exp (a^2*M/2) := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (weight_pos x s).le
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hM s) (sq_nonneg a)) (by norm_num)
    _ = _ := by rw [← Finset.sum_mul,sum_weight,one_mul]

 

theorem gaussian_sample_error {r : ℕ} (hr : 0<r) (x : ι → ℝ) (A : ι → κ → ℝ)
    {M : ℝ} (hM : ∀ s,kernel A s s≤M) {t : ℝ} (ht : 0<t) :
    |replicaMean x (samplePressure (r:=r) A)-gaussianLogAverage x A|≤
      Real.exp (2*M)*(t/(r:ℝ)+t⁻¹) := by
  let f (z : κ → ℝ) := replicaMean x (fun σ : Fin r → ι =>
    Real.log (empiricalMean (fun s => Real.exp (field A z s)) σ))
  let g (z : κ → ℝ) := Real.log (average x (fun s => Real.exp (field A z s)))
  have hf : Integrable f (gaussianLaw κ) := integrable_finsetSum _
    (fun σ _ => (integrable_empirical_log_exp hr A σ).const_mul _)
  have hg : Integrable g (gaussianLaw κ) := integrable_gaussianLogAverage x A
  have he : (∫ z,f z ∂gaussianLaw κ)=replicaMean x (samplePressure (r:=r) A) := by
    rw [show f=(fun z => ∑ σ : Fin r → ι, replicaWeight x σ*Real.log (empiricalMean (fun s => Real.exp (field A z s)) σ)) from rfl,
      integral_finsetSum _ (fun σ _ => (integrable_empirical_log_exp hr A σ).const_mul _)]
    simp only [integral_const_mul,integral_empirical_log_exp hr,replicaMean]
  have hsq (y : ℝ) : (Real.exp y)^2=Real.exp (2*y) := by
    rw [pow_two,← Real.exp_add]; congr 1; ring
  have hinv (y : ℝ) : (Real.exp y)⁻¹^2=Real.exp ((-2)*y) := by
    rw [← Real.exp_neg,hsq]; congr 1; ring
  have hb (z : κ → ℝ) : |f z-g z|≤
      (t/(r:ℝ))*average x (fun s => Real.exp (2*field A z s))+
        t⁻¹*average x (fun s => Real.exp ((-2)*field A z s)) := by
    simpa only [hsq,hinv] using empirical_log_mean_error hr x
      (fun s => Real.exp (field A z s)) (fun s => Real.exp_pos _) ht
  rw [← he]
  change |(∫ z,f z ∂gaussianLaw κ)-(∫ z,g z ∂gaussianLaw κ)|≤_
  rw [← integral_sub hf hg]
  apply abs_integral_le_integral_abs.trans
  have hh := integral_mono (hf.sub hg).abs
    (((integrable_average_exp_field x A 2).const_mul (t/(r:ℝ))).add
      ((integrable_average_exp_field x A (-2)).const_mul t⁻¹)) hb
  simp only [Pi.add_apply, Pi.sub_apply] at hh
  rw [integral_add ((integrable_average_exp_field x A 2).const_mul (t/(r:ℝ)))
    ((integrable_average_exp_field x A (-2)).const_mul t⁻¹),integral_const_mul,integral_const_mul] at hh
  have h1 := mul_le_mul_of_nonneg_left (integral_average_exp_field_le x A hM 2)
    (by positivity : 0≤t/(r:ℝ))
  have h2 := mul_le_mul_of_nonneg_left (integral_average_exp_field_le x A hM (-2)) (inv_nonneg.mpr ht.le)
  refine hh.trans ((add_le_add h1 h2).trans_eq ?_)
  ring_nf

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal MatrixOrder
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 def overlapMatrix {r : ℕ} (T : OverlapBlock r) : Matrix (Fin r) (Fin r) ℝ := fun i j => (T i j:ℝ)

lemma gramBlock_posSemidef {r : ℕ} {T : OverlapBlock r} (hT : T∈GramBlock r) :
    (overlapMatrix T).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.ext
    intro i j
    simpa [overlapMatrix,Matrix.conjTranspose_apply] using congrArg Subtype.val (hT.1 j i)
  · intro c
    have h := hT.2.2 c
    have he : star c ⬝ᵥ (overlapMatrix T).mulVec c=∑ i,∑ j,c i*c j*(T i j:ℝ) := by
      simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,overlapMatrix,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    exact h

lemma exists_gramFactor {r : ℕ} {T : OverlapBlock r} (hT : T∈GramBlock r) :
    ∃ A : Fin r → Fin r → ℝ, ∀ i j,kernel A i j=(T i j:ℝ) := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (gramBlock_posSemidef hT).nonneg
  refine ⟨fun i k => B k i,fun i j => ?_⟩
  have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ => M i j) hB
  simpa only [overlapMatrix,Matrix.mul_apply,Matrix.star_apply,star_trivial,kernel] using h.symm

def gramFactor {r : ℕ} (T : GramBlock r) : Fin r → Fin r → ℝ :=
  Classical.choose (exists_gramFactor T.property)

lemma kernel_gramFactor {r : ℕ} (T : GramBlock r) (i j : Fin r) :
    kernel (gramFactor T) i j=(T.val i j:ℝ) := Classical.choose_spec (exists_gramFactor T.property) i j

lemma gramFactor_diag {r : ℕ} (T : GramBlock r) (i : Fin r) :
    kernel (gramFactor T) i i=1 := (kernel_gramFactor T i i).trans (T.property.2.1 i)

 

def gramPressure {r : ℕ} (T : GramBlock r) (β : ℝ) : ℝ :=
  expected (fun i k => β*gramFactor T i k)-Real.log (r:ℝ)

lemma gramPressure_eq {r : ℕ} {κ : Type*} [Fintype κ] (T : GramBlock r) (β : ℝ)
    (A : Fin r → κ → ℝ) (hA : ∀ i j,kernel A i j=β^2*(T.val i j:ℝ)) :
    expected A-Real.log (r:ℝ)=gramPressure T β := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [gramPressure,expected,logPartition,partition,Finset.univ_eq_empty,Finset.sum_empty,Real.log_zero,integral_zero]
  · let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hr)
    unfold gramPressure
    congr 1
    apply expected_logPartition_eq_of_kernel
    intro i j
    rw [kernel_scale,kernel_gramFactor,hA]

lemma gramEntry_dist {r : ℕ} (T S : GramBlock r) (i j : Fin r) :
    |(T.val i j:ℝ)-(S.val i j:ℝ)|≤dist T S := by
  change dist (T.val i j) (S.val i j)≤dist T.val S.val
  exact (dist_le_pi_dist (T.val i) (S.val i) j).trans (dist_le_pi_dist T.val S.val i)

lemma gramPressure_lipschitz_bound {r : ℕ} (hr : 0<r) (T S : GramBlock r) (β : ℝ) :
    |gramPressure T β-gramPressure S β|≤(β^2*Real.pi/2)*dist T S := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  let A := fun i k => β*gramFactor S i k
  let B := fun i k => β*gramFactor T i k
  have hinc (i j : Fin r) : |ParisiInterpolation.increment B i j-ParisiInterpolation.increment A i j|≤
      2*β^2*dist T S := by
    simp only [increment_eq_kernel,B,A,kernel_scale,kernel_gramFactor,T.property.2.1,S.property.2.1]
    have he : β^2*1+β^2*1-2*(β^2*(T.val i j:ℝ))-
        (β^2*1+β^2*1-2*(β^2*(S.val i j:ℝ)))=
        -2*β^2*((T.val i j:ℝ)-(S.val i j:ℝ)) := by ring
    rw [he,abs_mul,abs_mul,abs_of_nonneg (sq_nonneg β)]
    norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact mul_le_mul_of_nonneg_left (gramEntry_dist T S i j) (by positivity)
  have h := expected_difference_le A B (by positivity : 0≤2*β^2*dist T S) hinc
  simpa only [gramPressure,sub_sub_sub_cancel_right] using h.trans_eq (by ring)

lemma continuous_gramPressure {r : ℕ} (hr : 0<r) (β : ℝ) : Continuous (fun T : GramBlock r => gramPressure T β) := by
  have h : LipschitzWith ⟨β^2*Real.pi/2,by positivity⟩ (fun T : GramBlock r => gramPressure T β) := by
    apply LipschitzWith.of_dist_le_mul
    intro T S
    exact gramPressure_lipschitz_bound hr T S β
  exact h.continuous

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

def signBool (b : Bool) : ℝ := if b then 1 else -1

lemma signBool_sq (b : Bool) : signBool b^2=1 := by cases b <;> norm_num [signBool]

def doubled (x z : ι → ℝ) : ι × Bool → ℝ := fun s => x s.1+signBool s.2*z s.1

omit [Nonempty ι] in
lemma partition_doubled (x z : ι → ℝ) :
    partition (doubled x z)=∑ s,Real.exp (x s)*(2*Real.cosh (z s)) := by
  simp only [partition,doubled,Fintype.sum_prod_type,Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro s _
  simp only [signBool,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,
    Real.cosh_eq,Real.exp_add]
  ring

lemma log_average_cosh (x z : ι → ℝ) :
    Real.log (average x (fun s => 2*Real.cosh (z s)))=logPartition (doubled x z)-logPartition x := by
  have hp : partition (doubled x z)=partition x*average x (fun s => 2*Real.cosh (z s)) := by
    rw [partition_doubled,partition_mul_average]
  rw [logPartition,hp,Real.log_mul (partition_pos x).ne'
    (average_pos x _ (fun s => by positivity)).ne']
  simp only [logPartition,add_sub_cancel_left]

def gaussianCoshAverage (x : ι → ℝ) (A : ι → κ → ℝ) : ℝ :=
  ∫ z,Real.log (average x (fun s => 2*Real.cosh (field A z s))) ∂gaussianLaw κ

lemma integrable_gaussianCoshAverage (x : ι → ℝ) (A : ι → κ → ℝ) :
    Integrable (fun z => Real.log (average x (fun s => 2*Real.cosh (field A z s)))) (gaussianLaw κ) := by
  simp_rw [log_average_cosh]
  exact (integrable_logPartition (fun s : ι × Bool => (integrable_const (x s.1)).add
    ((integrable_field A s.1).const_mul (signBool s.2)))).sub (integrable_const _)

omit [Fintype ι] [Nonempty ι] in
lemma empirical_log_cosh {r : ℕ} (hr : 0<r) (f : ι → ℝ) (σ : Fin r → ι) :
    Real.log (empiricalMean (fun s => 2*Real.cosh (f s)) σ)=
      logPartition (fun s : Fin r × Bool => signBool s.2*f (σ s.1))-Real.log (r:ℝ) := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  have he : partition (fun s : Fin r × Bool => signBool s.2*f (σ s.1))=
      ∑ i,2*Real.cosh (f (σ i)) := by
    have h := partition_doubled (fun _ : Fin r => 0) (fun i => f (σ i))
    change partition (fun s : Fin r × Bool => 0+signBool s.2*f (σ s.1))=∑ i,Real.exp 0*(2*Real.cosh (f (σ i))) at h
    simp only [zero_add,Real.exp_zero,one_mul] at h
    exact h
  unfold logPartition empiricalMean
  rw [← he,Real.log_div (partition_pos _).ne' (Nat.cast_ne_zero.mpr hr.ne')]

omit [Fintype ι] [Nonempty ι] in
lemma integrable_empirical_log_cosh {r : ℕ} (hr : 0<r) (A : ι → κ → ℝ) (σ : Fin r → ι) :
    Integrable (fun z => Real.log (empiricalMean (fun s => 2*Real.cosh (field A z s)) σ)) (gaussianLaw κ) := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  simp_rw [empirical_log_cosh hr]
  exact (integrable_logPartition (fun s : Fin r × Bool => (integrable_field A (σ s.1)).const_mul (signBool s.2))).sub (integrable_const _)

def sampleCoshPressure {r : ℕ} (A : ι → κ → ℝ) (σ : Fin r → ι) : ℝ :=
  expected (fun s : Fin r × Bool => fun k => signBool s.2*A (σ s.1) k)-Real.log (r:ℝ)

omit [Fintype ι] [Nonempty ι] in
lemma integral_empirical_log_cosh {r : ℕ} (hr : 0<r) (A : ι → κ → ℝ) (σ : Fin r → ι) :
    (∫ z,Real.log (empiricalMean (fun s => 2*Real.cosh (field A z s)) σ) ∂gaussianLaw κ)=sampleCoshPressure A σ := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  simp_rw [empirical_log_cosh hr]
  rw [integral_sub (integrable_logPartition (fun s : Fin r × Bool => (integrable_field A (σ s.1)).const_mul (signBool s.2))) (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]
  unfold sampleCoshPressure expected
  congr 2
  ext z
  congr 1
  ext s
  change signBool s.2*(∑ k,A (σ s.1) k*z k)=∑ k,(signBool s.2*A (σ s.1) k)*z k
  simp only [Finset.mul_sum,mul_assoc]

lemma cosh_squared_bound (y : ℝ) : (2*Real.cosh y)^2≤2*(Real.exp (2*y)+Real.exp ((-2)*y)) := by
  have h : 0≤(Real.exp y-Real.exp (-y))^2 := sq_nonneg _
  have he : (Real.exp y)^2=Real.exp (2*y) := by rw [pow_two,← Real.exp_add]; congr 1; ring
  have he' : (Real.exp (-y))^2=Real.exp ((-2)*y) := by rw [pow_two,← Real.exp_add]; congr 1; ring
  rw [Real.cosh_eq]
  nlinarith [he,he']

lemma cosh_inv_squared_bound (y : ℝ) : (2*Real.cosh y)⁻¹^2≤1 := by
  have hc := Real.one_le_cosh y
  have hp : 0<2*Real.cosh y := by positivity
  have h : (2*Real.cosh y)⁻¹≤1 := (inv_le_one₀ hp).mpr (by linarith)
  exact (sq_le_one_iff_abs_le_one _).mpr (by rwa [abs_of_nonneg (inv_nonneg.mpr hp.le)])

lemma average_cosh_squared_bound (x : ι → ℝ) (f : ι → ℝ) :
    average x (fun s => (2*Real.cosh (f s))^2)≤
      2*(average x (fun s => Real.exp (2*f s))+average x (fun s => Real.exp ((-2)*f s))) := by
  change (∑ s,weight x s*(2*Real.cosh (f s))^2)≤_
  calc
    _ ≤ ∑ s,weight x s*(2*(Real.exp (2*f s)+Real.exp ((-2)*f s))) := by
      exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (cosh_squared_bound (f s)) (weight_pos x s).le
    _ = _ := by simp only [average,Finset.mul_sum,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro s _; ring

lemma average_cosh_inverse_bound (x : ι → ℝ) (f : ι → ℝ) :
    average x (fun s => (2*Real.cosh (f s))⁻¹^2)≤1 := by
  calc
    _ ≤ ∑ s,weight x s*1 := Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (cosh_inv_squared_bound (f s)) (weight_pos x s).le
    _ = _ := by simp only [mul_one,sum_weight]

theorem gaussian_cosh_sample_error {r : ℕ} (hr : 0<r) (x : ι → ℝ) (A : ι → κ → ℝ)
    {M : ℝ} (hM : ∀ s,kernel A s s≤M) {t : ℝ} (ht : 0<t) :
    |replicaMean x (sampleCoshPressure (r:=r) A)-gaussianCoshAverage x A|≤
      (4*Real.exp (2*M))*(t/(r:ℝ))+t⁻¹ := by
  let f (z : κ → ℝ) := replicaMean x (fun σ : Fin r → ι =>
    Real.log (empiricalMean (fun s => 2*Real.cosh (field A z s)) σ))
  let g (z : κ → ℝ) := Real.log (average x (fun s => 2*Real.cosh (field A z s)))
  have hf : Integrable f (gaussianLaw κ) := integrable_finsetSum _
    (fun σ _ => (integrable_empirical_log_cosh hr A σ).const_mul _)
  have hg : Integrable g (gaussianLaw κ) := integrable_gaussianCoshAverage x A
  have he : (∫ z,f z ∂gaussianLaw κ)=replicaMean x (sampleCoshPressure (r:=r) A) := by
    rw [show f=(fun z => ∑ σ : Fin r → ι, replicaWeight x σ*Real.log (empiricalMean (fun s => 2*Real.cosh (field A z s)) σ)) from rfl,
      integral_finsetSum _ (fun σ _ => (integrable_empirical_log_cosh hr A σ).const_mul _)]
    simp only [integral_const_mul,integral_empirical_log_cosh hr,replicaMean]
  have hb (z : κ → ℝ) : |f z-g z|≤
      (2*t/(r:ℝ))*(average x (fun s => Real.exp (2*field A z s))+
        average x (fun s => Real.exp ((-2)*field A z s)))+t⁻¹ := by
    have h := empirical_log_mean_error hr x (fun s => 2*Real.cosh (field A z s)) (fun s => by positivity) ht
    have h1 := mul_le_mul_of_nonneg_left (average_cosh_squared_bound x (field A z)) (by positivity : 0≤t/(r:ℝ))
    have h2 := mul_le_mul_of_nonneg_left (average_cosh_inverse_bound x (field A z)) (inv_nonneg.mpr ht.le)
    exact h.trans ((add_le_add h1 h2).trans_eq (by ring))
  rw [← he]
  change |(∫ z,f z ∂gaussianLaw κ)-(∫ z,g z ∂gaussianLaw κ)|≤_
  rw [← integral_sub hf hg]
  apply abs_integral_le_integral_abs.trans
  have hh := integral_mono (hf.sub hg).abs
    (((integrable_average_exp_field x A 2).add (integrable_average_exp_field x A (-2))).const_mul (2*t/(r:ℝ)) |>.add (integrable_const t⁻¹)) hb
  simp only [Pi.add_apply,Pi.sub_apply] at hh
  have hi : Integrable (fun z => average x (fun s => Real.exp (2*field A z s))+average x (fun s => Real.exp ((-2)*field A z s))) (gaussianLaw κ) :=
    (integrable_average_exp_field x A 2).add (integrable_average_exp_field x A (-2))
  rw [integral_add (hi.const_mul (2*t/(r:ℝ))) (integrable_const t⁻¹),
    integral_const_mul,integral_add (integrable_average_exp_field x A 2) (integrable_average_exp_field x A (-2)),
    integral_const,probReal_univ,one_smul] at hh
  have h1 := integral_average_exp_field_le x A hM 2
  have h2 := integral_average_exp_field_le x A hM (-2)
  have h := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : 0≤2*t/(r:ℝ))
  apply hh.trans ((add_le_add h (le_refl t⁻¹)).trans_eq _)
  norm_num only [pow_two,neg_mul_neg,mul_one] 
  congr 1
  ring_nf

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def coshGramCoeff {r : ℕ} (T : GramBlock r) (β : ℝ) : (Fin r × Bool) → Fin r → ℝ :=
  fun s k => signBool s.2*β*gramFactor T s.1 k

lemma kernel_coshGramCoeff {r : ℕ} (T : GramBlock r) (β : ℝ) (s t : Fin r × Bool) :
    kernel (coshGramCoeff T β) s t=signBool s.2*signBool t.2*β^2*(T.val s.1 t.1:ℝ) := by
  have he : kernel (coshGramCoeff T β) s t=
      (signBool s.2*signBool t.2*β^2)*kernel (gramFactor T) s.1 t.1 := by
    simp only [kernel,coshGramCoeff,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,kernel_gramFactor]

lemma diag_coshGramCoeff {r : ℕ} (T : GramBlock r) (β : ℝ) (s : Fin r × Bool) :
    kernel (coshGramCoeff T β) s s=β^2 := by
  rw [kernel_coshGramCoeff,T.property.2.1 s.1,← pow_two,signBool_sq,one_mul,mul_one]

def squareGramCoeff {r : ℕ} (T : GramBlock r) (β : ℝ) : Fin r → (Fin r × Fin r) → ℝ :=
  fun i k => (β/Real.sqrt 2)*gramFactor T i k.1*gramFactor T i k.2

lemma kernel_squareGramCoeff {r : ℕ} (T : GramBlock r) (β : ℝ) (i j : Fin r) :
    kernel (squareGramCoeff T β) i j=β^2/2*(T.val i j:ℝ)^2 := by
  have he : kernel (squareGramCoeff T β) i j=
      (β/Real.sqrt 2)^2*(kernel (gramFactor T) i j)^2 := by
    simp only [kernel,squareGramCoeff,Fintype.sum_prod_type,pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he,kernel_gramFactor,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

lemma diag_squareGramCoeff {r : ℕ} (T : GramBlock r) (β : ℝ) (i : Fin r) :
    kernel (squareGramCoeff T β) i i=β^2/2 := by
  rw [kernel_squareGramCoeff,T.property.2.1 i,one_pow,mul_one]

def coshGramPressure {r : ℕ} (T : GramBlock r) (β : ℝ) : ℝ :=
  expected (coshGramCoeff T β)-Real.log (r:ℝ)

def squareGramPressure {r : ℕ} (T : GramBlock r) (β : ℝ) : ℝ :=
  expected (squareGramCoeff T β)-Real.log (r:ℝ)

def cavityGramObservable {r : ℕ} (T : GramBlock r) (β : ℝ) : ℝ :=
  coshGramPressure T β-squareGramPressure T β

lemma abs_signBool (b : Bool) : |signBool b|=1 := by cases b <;> norm_num [signBool]

lemma cosh_kernel_dist {r : ℕ} (T S : GramBlock r) (β : ℝ) (s t : Fin r × Bool) :
    |kernel (coshGramCoeff T β) s t-kernel (coshGramCoeff S β) s t|≤β^2*dist T S := by
  rw [kernel_coshGramCoeff,kernel_coshGramCoeff,← mul_sub,abs_mul,abs_mul,abs_mul,
    abs_signBool,abs_signBool,abs_of_nonneg (sq_nonneg β),one_mul,one_mul]
  exact mul_le_mul_of_nonneg_left (gramEntry_dist T S s.1 t.1) (sq_nonneg β)

lemma coshGramPressure_lipschitz {r : ℕ} (hr : 0<r) (T S : GramBlock r) (β : ℝ) :
    |coshGramPressure T β-coshGramPressure S β|≤(β^2*Real.pi/2)*dist T S := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  have hi (s t : Fin r × Bool) :
      |ParisiInterpolation.increment (coshGramCoeff T β) s t-ParisiInterpolation.increment (coshGramCoeff S β) s t|≤2*β^2*dist T S := by
    rw [increment_eq_kernel,increment_eq_kernel,diag_coshGramCoeff,diag_coshGramCoeff,diag_coshGramCoeff,diag_coshGramCoeff]
    have he (a b : ℝ) : β^2+β^2-2*a-(β^2+β^2-2*b)=(-2)*(a-b) := by ring
    rw [he,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    have h := mul_le_mul_of_nonneg_left (cosh_kernel_dist T S β s t) (by norm_num : (0:ℝ)≤2)
    simpa only [mul_assoc] using h
  have h := expected_difference_le (coshGramCoeff S β) (coshGramCoeff T β)
    (by positivity : 0≤2*β^2*dist T S) hi
  simpa only [coshGramPressure,sub_sub_sub_cancel_right] using h.trans_eq (by ring)

lemma overlap_square_dist (x y : OverlapEntry) : |(x:ℝ)^2-(y:ℝ)^2|≤2*|(x:ℝ)-(y:ℝ)| := by
  have hx : |(x:ℝ)|≤1 := abs_le.mpr x.property
  have hy : |(y:ℝ)|≤1 := abs_le.mpr y.property
  have hs : |(x:ℝ)+(y:ℝ)|≤2 := (abs_add_le _ _).trans (by linarith)
  rw [show (x:ℝ)^2-(y:ℝ)^2=((x:ℝ)+(y:ℝ))*((x:ℝ)-(y:ℝ)) by ring,abs_mul]
  exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)

lemma square_kernel_dist {r : ℕ} (T S : GramBlock r) (β : ℝ) (i j : Fin r) :
    |kernel (squareGramCoeff T β) i j-kernel (squareGramCoeff S β) i j|≤β^2*dist T S := by
  rw [kernel_squareGramCoeff,kernel_squareGramCoeff,← mul_sub,abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ)≤β^2/2)]
  have h := (overlap_square_dist (T.val i j) (S.val i j)).trans
    (mul_le_mul_of_nonneg_left (gramEntry_dist T S i j) (by norm_num : (0:ℝ)≤2))
  exact (mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ)≤β^2/2)).trans_eq (by ring)

lemma squareGramPressure_lipschitz {r : ℕ} (hr : 0<r) (T S : GramBlock r) (β : ℝ) :
    |squareGramPressure T β-squareGramPressure S β|≤(β^2*Real.pi/2)*dist T S := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  have hi (i j : Fin r) :
      |ParisiInterpolation.increment (squareGramCoeff T β) i j-ParisiInterpolation.increment (squareGramCoeff S β) i j|≤2*β^2*dist T S := by
    rw [increment_eq_kernel,increment_eq_kernel,diag_squareGramCoeff,diag_squareGramCoeff,diag_squareGramCoeff,diag_squareGramCoeff]
    have he (a b : ℝ) : β^2/2+β^2/2-2*a-(β^2/2+β^2/2-2*b)=(-2)*(a-b) := by ring
    rw [he,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    have h := mul_le_mul_of_nonneg_left (square_kernel_dist T S β i j) (by norm_num : (0:ℝ)≤2)
    simpa only [mul_assoc] using h
  have h := expected_difference_le (squareGramCoeff S β) (squareGramCoeff T β)
    (by positivity : 0≤2*β^2*dist T S) hi
  simpa only [squareGramPressure,sub_sub_sub_cancel_right] using h.trans_eq (by ring)

lemma continuous_coshGramPressure {r : ℕ} (hr : 0<r) (β : ℝ) :
    Continuous (fun T : GramBlock r => coshGramPressure T β) := by
  have h : LipschitzWith ⟨β^2*Real.pi/2,by positivity⟩ (fun T : GramBlock r => coshGramPressure T β) := by
    apply LipschitzWith.of_dist_le_mul
    intro T S
    exact coshGramPressure_lipschitz hr T S β
  exact h.continuous

lemma continuous_squareGramPressure {r : ℕ} (hr : 0<r) (β : ℝ) :
    Continuous (fun T : GramBlock r => squareGramPressure T β) := by
  have h : LipschitzWith ⟨β^2*Real.pi/2,by positivity⟩ (fun T : GramBlock r => squareGramPressure T β) := by
    apply LipschitzWith.of_dist_le_mul
    intro T S
    exact squareGramPressure_lipschitz hr T S β
  exact h.continuous

lemma continuous_cavityGramObservable {r : ℕ} (hr : 0<r) (β : ℝ) :
    Continuous (fun T : GramBlock r => cavityGramObservable T β) :=
  (continuous_coshGramPressure hr β).sub (continuous_squareGramPressure hr β)

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι κ κ₂ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype κ₂]

omit [Fintype ι] [Nonempty ι] in
lemma integrable_field_prod (A : ι → κ → ℝ) (B : ι → κ₂ → ℝ) (s : ι) :
    Integrable (fun p : (κ → ℝ) × (κ₂ → ℝ) => field A p.1 s+field B p.2 s)
      ((gaussianLaw κ).prod (gaussianLaw κ₂)) :=
  ((integrable_field A s).comp_fst _).add ((integrable_field B s).comp_snd _)

lemma expected_independent_integral (A : ι → κ → ℝ) (B : ι → κ₂ → ℝ) :
    expected (independentCoeff A B)=
      ∫ x,∫ y,logPartition (fun s => field A x s+field B y s) ∂gaussianLaw κ₂ ∂gaussianLaw κ := by
  let T : ((κ → ℝ) × (κ₂ → ℝ)) ≃ᵐ ((κ ⊕ κ₂) → ℝ) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ κ₂ => ℝ)).symm
  have hp : MeasurePreserving T ((gaussianLaw κ).prod (gaussianLaw κ₂)) (gaussianLaw (κ ⊕ κ₂)) :=
    measurePreserving_sumPiEquivProdPi_symm (fun _ => gaussianReal 0 1)
  unfold expected
  rw [← hp.integral_comp']
  have he (p : (κ → ℝ) × (κ₂ → ℝ)) : field (independentCoeff A B) (T p)=fun s => field A p.1 s+field B p.2 s := by
    ext s
    simp only [field,independentCoeff,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
    rfl
  simp_rw [he]
  exact integral_prod _ (integrable_logPartition (integrable_field_prod A B))

lemma integrable_logAverage_prod (A : ι → κ → ℝ) (B : ι → κ₂ → ℝ) :
    Integrable (fun p : (κ → ℝ) × (κ₂ → ℝ) =>
      Real.log (average (field A p.1) (fun s => Real.exp (field B p.2 s))))
        ((gaussianLaw κ).prod (gaussianLaw κ₂)) := by
  simp_rw [log_average_exp]
  exact (integrable_logPartition (integrable_field_prod A B)).sub
    ((integrable_logPartition (integrable_field A)).comp_fst _)

lemma integrable_gaussianLogAverage_field (A : ι → κ → ℝ) (B : ι → κ₂ → ℝ) :
    Integrable (fun x => gaussianLogAverage (field A x) B) (gaussianLaw κ) :=
  (integrable_logAverage_prod A B).integral_prod_left

lemma integral_gaussianLogAverage (A : ι → κ → ℝ) (B : ι → κ₂ → ℝ) :
    (∫ x,gaussianLogAverage (field A x) B ∂gaussianLaw κ)=
      expected (independentCoeff A B)-expected A := by
  unfold gaussianLogAverage
  rw [← integral_prod _ (integrable_logAverage_prod A B)]
  simp_rw [log_average_exp]
  rw [integral_sub (integrable_logPartition (integrable_field_prod A B))
    ((integrable_logPartition (integrable_field A)).comp_fst _),
    integral_prod _ (integrable_logPartition (integrable_field_prod A B)),
    ← expected_independent_integral,integral_fun_fst (fun x : κ → ℝ => logPartition (field A x))]
  simp only [probReal_univ,one_smul]
  rfl

lemma integrable_coshAverage_prod (A : ι → κ → ℝ) (B : ι → κ₂ → ℝ) :
    Integrable (fun p : (κ → ℝ) × (κ₂ → ℝ) =>
      Real.log (average (field A p.1) (fun s => 2*Real.cosh (field B p.2 s))))
        ((gaussianLaw κ).prod (gaussianLaw κ₂)) := by
  simp_rw [log_average_cosh]
  exact (integrable_logPartition (fun s : ι × Bool =>
    ((integrable_field A s.1).comp_fst _).add (((integrable_field B s.1).comp_snd _).const_mul (signBool s.2)))).sub
      ((integrable_logPartition (integrable_field A)).comp_fst _)

lemma integrable_gaussianCoshAverage_field (A : ι → κ → ℝ) (B : ι → κ₂ → ℝ) :
    Integrable (fun x => gaussianCoshAverage (field A x) B) (gaussianLaw κ) :=
  (integrable_coshAverage_prod A B).integral_prod_left

def cavityDoubledCoeff (A : ι → κ → ℝ) (B : ι → κ₂ → ℝ) : ι × Bool → (κ ⊕ κ₂) → ℝ :=
  independentCoeff (fun s => A s.1) (fun s k => signBool s.2*B s.1 k)

lemma integral_gaussianCoshAverage (A : ι → κ → ℝ) (B : ι → κ₂ → ℝ) :
    (∫ x,gaussianCoshAverage (field A x) B ∂gaussianLaw κ)=
      expected (cavityDoubledCoeff A B)-expected A := by
  unfold gaussianCoshAverage
  rw [← integral_prod _ (integrable_coshAverage_prod A B)]
  simp_rw [log_average_cosh]
  have hi : Integrable (fun p : (κ → ℝ) × (κ₂ → ℝ) =>
      logPartition (doubled (field A p.1) (field B p.2)))
        ((gaussianLaw κ).prod (gaussianLaw κ₂)) := integrable_logPartition (fun s : ι × Bool =>
    ((integrable_field A s.1).comp_fst (gaussianLaw κ₂)).add
      (((integrable_field B s.1).comp_snd (gaussianLaw κ)).const_mul (signBool s.2)))
  rw [integral_sub hi ((integrable_logPartition (integrable_field A)).comp_fst _),
    integral_prod _ hi,integral_fun_fst (fun x : κ → ℝ => logPartition (field A x))]
  simp only [probReal_univ,one_smul]
  unfold cavityDoubledCoeff
  rw [expected_independent_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  ext s
  change field A x s.1+signBool s.2*(∑ k,B s.1 k*y k)=
    field A x s.1+∑ k,(signBool s.2*B s.1 k)*y k
  simp only [Finset.mul_sum,mul_assoc]

theorem averaged_gaussian_sample_error {r : ℕ} (hr : 0<r) (A : ι → κ → ℝ) (B : ι → κ₂ → ℝ)
    {M : ℝ} (hM : ∀ s,kernel B s s≤M) {t : ℝ} (ht : 0<t) :
    |averagedReplica A (samplePressure (r:=r) B)-
      (expected (independentCoeff A B)-expected A)|≤Real.exp (2*M)*(t/(r:ℝ)+t⁻¹) := by
  rw [← integral_gaussianLogAverage]
  unfold averagedReplica
  rw [← integral_sub (integrable_field_replicaMean A _) (integrable_gaussianLogAverage_field A B)]
  apply abs_integral_le_integral_abs.trans
  have h := integral_mono ((integrable_field_replicaMean A _).sub (integrable_gaussianLogAverage_field A B)).abs
    (integrable_const (Real.exp (2*M)*(t/(r:ℝ)+t⁻¹))) (fun x => gaussian_sample_error hr (field A x) B hM ht)
  simpa only [Pi.sub_apply,integral_const,probReal_univ,one_smul] using h

theorem averaged_gaussian_cosh_sample_error {r : ℕ} (hr : 0<r) (A : ι → κ → ℝ) (B : ι → κ₂ → ℝ)
    {M : ℝ} (hM : ∀ s,kernel B s s≤M) {t : ℝ} (ht : 0<t) :
    |averagedReplica A (sampleCoshPressure (r:=r) B)-
      (expected (cavityDoubledCoeff A B)-expected A)|≤(4*Real.exp (2*M))*(t/(r:ℝ))+t⁻¹ := by
  rw [← integral_gaussianCoshAverage]
  unfold averagedReplica
  rw [← integral_sub (integrable_field_replicaMean A _) (integrable_gaussianCoshAverage_field A B)]
  apply abs_integral_le_integral_abs.trans
  have h := integral_mono ((integrable_field_replicaMean A _).sub (integrable_gaussianCoshAverage_field A B)).abs
    (integrable_const ((4*Real.exp (2*M))*(t/(r:ℝ))+t⁻¹)) (fun x => gaussian_cosh_sample_error hr (field A x) B hM ht)
  simpa only [Pi.sub_apply,integral_const,probReal_univ,one_smul] using h

end SKCavity

end

end OAI
