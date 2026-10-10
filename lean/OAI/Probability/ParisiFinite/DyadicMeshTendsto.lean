import Mathlib
import OAI.Probability.ParisiFinite.OverlapDiscountMono

namespace OAI

/-! Dyadic Mesh Tendsto. -/

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
open scoped BigOperators Topology NNReal ENNReal MatrixOrder
open scoped BigOperators Topology NNReal ENNReal ContDiff
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

lemma dyadicMesh_tendsto (d : ℝ≥0) :
    Tendsto (fun n => (dyadicMesh d n:ℝ)) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ)<2 by norm_num)
  have hh := (tendsto_inv_atTop_zero.comp hp).const_mul (d:ℝ)
  change Tendsto (fun n : ℕ => (d:ℝ)/(2:ℝ)^n) atTop (𝓝 0)
  simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using hh

lemma dyadicMesh_le (d : ℝ≥0) (n : ℕ) : dyadicMesh d n≤d := by
  apply div_le_self (show 0≤d from zero_le)
  exact one_le_pow₀ (by norm_num : (1:ℝ≥0)≤2)

lemma gaussianSmallError_dyadic_tendsto (β : ℝ) (d : ℝ≥0) :
    Tendsto (fun n => gaussianSmallError β (Real.sqrt (dyadicMesh d n))) atTop (𝓝 0) := by
  let s (n : ℕ) := Real.sqrt (dyadicMesh d n)
  let L : ℝ≥0 := Real.toNNReal (Real.sqrt d)
  have hs (n : ℕ) : |s n|≤Real.sqrt d := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast dyadicMesh_le d n)
  have ht : Tendsto s atTop (𝓝 (0:ℝ)) := by
    simpa only [Real.sqrt_zero,Function.comp_def,s] using Real.continuous_sqrt.continuousAt.tendsto.comp (dyadicMesh_tendsto d)
  have hF (n : ℕ) : LipschitzWith L (fun z : ℝ => |s n| * |z|) :=
    (abs_scaled_lipschitz (s n)).weaken (Real.toNNReal_mono (hs n))
  have hf : LipschitzWith L (fun _ : ℝ => (0:ℝ)) := (LipschitzWith.const (0:ℝ)).weaken (by positivity)
  have hh := step_tendsto hF hf (fun z => by simpa using (ht.abs).mul_const |z|) β 1 0
  simpa only [step,zero_add,one_mul,logMean_const,gaussianSmallError,s] using hh

 

def dyadicEvolution (γ : ℝ≥0 → ℝ≥0) (t d : ℝ≥0) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨆ n : ℕ,evolve (dyadicSchedule γ false t d n) f x

lemma dyadic_low_monotone {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (t d : ℝ≥0) (x : ℝ) :
    Monotone (fun n => evolve (dyadicSchedule γ false t d n) f x) :=
  monotone_nat_of_le_succ (fun n => dyadicSchedule_low_refine hf hγ t d n x)

lemma dyadic_high_antitone {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (t d : ℝ≥0) (x : ℝ) :
    Antitone (fun n => evolve (dyadicSchedule γ true t d n) f x) :=
  antitone_nat_of_succ_le (fun n => dyadicSchedule_high_refine hf hγ t d n x)

lemma dyadic_low_bddAbove {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (t d : ℝ≥0) (x : ℝ) :
    BddAbove (Set.range (fun n => evolve (dyadicSchedule γ false t d n) f x)) := by
  refine ⟨evolve (dyadicSchedule γ true t d 0) f x,?_⟩
  rintro _ ⟨n,rfl⟩
  exact (dyadicSchedule_low_le_high hf hγ t d n x).trans (dyadic_high_antitone hf hγ t d x (Nat.zero_le n))

lemma dyadic_low_tendsto {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (t d : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => evolve (dyadicSchedule γ false t d n) f x) atTop
      (𝓝 (dyadicEvolution γ t d f x)) :=
  tendsto_atTop_ciSup (dyadic_low_monotone hf hγ t d x) (dyadic_low_bddAbove hf hγ t d x)

lemma dyadic_high_tendsto {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ} (hb : ∀ t,(γ t:ℝ)≤β)
    (t d : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => evolve (dyadicSchedule γ true t d n) f x) atTop
      (𝓝 (dyadicEvolution γ t d f x)) := by
  have he : Tendsto (fun n => 2*gaussianSmallError β (Real.sqrt (dyadicMesh d n))) atTop (𝓝 (0:ℝ)) := by
    simpa using (gaussianSmallError_dyadic_tendsto β d).const_mul 2
  have hl := dyadic_low_tendsto hf hγ t d x
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl
    (by simpa only [add_zero] using hl.add he)
  · exact fun n => dyadicSchedule_low_le_high hf hγ t d n x
  · intro n
    have hh := (abs_le.mp (dyadicSchedule_grid_error hb t d n hf x)).1
    linarith

lemma dyadicEvolution_lipschitz {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (t d : ℝ≥0) :
    LipschitzWith L (dyadicEvolution γ t d f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto ((dyadic_low_tendsto hf hγ t d x).dist (dyadic_low_tendsto hf hγ t d y))
  exact Eventually.of_forall fun n => (evolve_lipschitz hf _).dist_le_mul x y

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

def uniformLower (γ : ℝ≥0 → ℝ≥0) (t d : ℝ≥0) (N : ℕ) : Schedule :=
  List.ofFn (fun k : Fin N => (γ (t+d*(k.val:ℝ≥0)/N),d/N))

lemma dyadicSchedule_eq_uniform (γ : ℝ≥0 → ℝ≥0) (t d : ℝ≥0) (n : ℕ) :
    dyadicSchedule γ false t d n=uniformLower γ t d (2^n) := by
  induction n generalizing t d with
  | zero => simp [dyadicSchedule,uniformLower,List.ofFn_succ]
  | succ n ih =>
    have he : 2^(n+1)=2^n+2^n := by rw [pow_succ]; omega
    rw [dyadicSchedule,ih,ih,he]
    unfold uniformLower
    rw [List.ofFn_add]
    congr 1
    · apply congrArg List.ofFn
      funext k
      simp only [Fin.val_castLE,Nat.cast_add]
      apply Prod.ext
      · apply congrArg γ
        ring
      · ring
    · apply congrArg List.ofFn
      funext k
      simp only [Fin.val_natAdd,Nat.cast_add]
      apply Prod.ext
      · apply congrArg γ
        have hn : ((2^n:ℕ):ℝ≥0)≠0 := by positivity
        field_simp
        ring
      · ring

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

lemma width_append (ls rs : Schedule) : width (ls++rs)=width ls+width rs := by simp [width]
lemma width_cons (a d : ℝ≥0) (ls : Schedule) : width ((a,d)::ls)=(d:ℝ)+width ls := by simp [width]
lemma penalty_append (t : ℝ) (ls rs : Schedule) :
    penalty t (ls++rs)=penalty t ls+penalty (t+width ls) rs := by
  induction ls generalizing t with
  | nil => simp [penalty,width]
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    simp only [List.cons_append,penalty,ih,width_cons,add_assoc]

lemma dyadicSchedule_width (γ : ℝ≥0 → ℝ≥0) (u : Bool) (t d : ℝ≥0) (n : ℕ) :
    width (dyadicSchedule γ u t d n)=d := by
  induction n generalizing t d with
  | zero => simp [dyadicSchedule,width]
  | succ n ih => rw [dyadicSchedule,width_append,ih,ih]; change (d:ℝ)/2+d/2=d; ring

lemma dyadic_penalty_succ (γ : ℝ≥0 → ℝ≥0) (u : Bool) (t d : ℝ≥0) (n : ℕ) :
    penalty t (dyadicSchedule γ u t d (n+1))=
      penalty t (dyadicSchedule γ u t (d/2) n)+penalty (t+d/2) (dyadicSchedule γ u (t+d/2) (d/2) n) := by
  rw [dyadicSchedule,penalty_append,dyadicSchedule_width]
  rfl

 
def coefficientPenalty (γ : ℝ≥0 → ℝ≥0) (t d : ℝ≥0) : ℝ :=
  ∫ s in (t:ℝ)..(t+d:ℝ≥0), s*(γ (Real.toNNReal s):ℝ)/2

lemma coefficient_integrable {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (a b : ℝ) :
    IntervalIntegrable (fun s => s*(γ (Real.toNNReal s):ℝ)/2) volume a b := by
  have hm : Monotone (fun s : ℝ => (γ (Real.toNNReal s):ℝ)) :=
    fun x y hxy => by exact_mod_cast hγ (Real.toNNReal_mono hxy)
  exact (hm.intervalIntegrable.continuousOn_mul continuous_id.continuousOn).div_const 2

lemma coefficientPenalty_split {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (t d : ℝ≥0) :
    coefficientPenalty γ t d=coefficientPenalty γ t (d/2)+coefficientPenalty γ (t+d/2) (d/2) := by
  have he : t+d/2+d/2=t+d := by ring
  simp only [coefficientPenalty,he]
  exact (intervalIntegral.integral_add_adjacent_intervals (coefficient_integrable hγ _ _)
    (coefficient_integrable hγ _ _)).symm

lemma constant_coefficient_integral (a t d : ℝ) :
    (∫ s in t..t+d,s*a/2)=a*((t+d)^2-t^2)/4 := by
  rw [intervalIntegral.integral_div,intervalIntegral.integral_mul_const,integral_id]
  ring

lemma coefficientPenalty_base_bounds {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (t d : ℝ≥0) :
    (γ t:ℝ)*(((t:ℝ)+d)^2-t^2)/4≤coefficientPenalty γ t d ∧
      coefficientPenalty γ t d≤(γ (t+d):ℝ)*(((t:ℝ)+d)^2-t^2)/4 := by
  have hab : (t:ℝ)≤(t+d:ℝ≥0) := by change (t:ℝ)≤t+d; linarith [d.coe_nonneg]
  have hi (a : ℝ) : IntervalIntegrable (fun s : ℝ => s*a/2) volume (t:ℝ) (t+d:ℝ≥0) :=
    (by fun_prop : Continuous (fun s : ℝ => s*a/2)).intervalIntegrable _ _
  constructor
  · rw [← constant_coefficient_integral]
    exact intervalIntegral.integral_mono_on hab (hi _) (coefficient_integrable hγ _ _) (fun s hs => by
      have hts : t≤Real.toNNReal s := by exact_mod_cast (show (t:ℝ)≤(Real.toNNReal s:ℝ) by rw [Real.coe_toNNReal _ (t.coe_nonneg.trans hs.1)]; exact hs.1)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hγ hts) (t.coe_nonneg.trans hs.1)) (by norm_num))
  · rw [← constant_coefficient_integral]
    exact intervalIntegral.integral_mono_on hab (coefficient_integrable hγ _ _) (hi _) (fun s hs => by
      have hst : Real.toNNReal s≤t+d := by exact_mod_cast (show (Real.toNNReal s:ℝ)≤(t+d:ℝ≥0) by rw [Real.coe_toNNReal _ (t.coe_nonneg.trans hs.1)]; exact hs.2)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hγ hst) (t.coe_nonneg.trans hs.1)) (by norm_num))

lemma dyadic_penalty_bounds {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (t d : ℝ≥0) (n : ℕ) :
    penalty t (dyadicSchedule γ false t d n)≤coefficientPenalty γ t d ∧
      coefficientPenalty γ t d≤penalty t (dyadicSchedule γ true t d n) := by
  induction n generalizing t d with
  | zero => simpa [dyadicSchedule,penalty] using coefficientPenalty_base_bounds hγ t d
  | succ n ih =>
    rw [dyadic_penalty_succ,dyadic_penalty_succ,coefficientPenalty_split hγ]
    exact ⟨add_le_add (ih t (d/2)).1 (ih (t+d/2) (d/2)).1,
      add_le_add (ih t (d/2)).2 (ih (t+d/2) (d/2)).2⟩

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

lemma dyadic_penalty_difference {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (t d : ℝ≥0) (n : ℕ) :
    penalty t (dyadicSchedule γ true t d n)-penalty t (dyadicSchedule γ false t d n)≤
      ((t:ℝ)+d)*(dyadicMesh d n:ℝ)*((γ (t+d):ℝ)-γ t)/2 := by
  induction n generalizing t d with
  | zero =>
    have ha : (γ t:ℝ)≤γ (t+d) := by exact_mod_cast hγ (le_add_of_nonneg_right (show 0≤d from zero_le))
    simp [dyadicSchedule,penalty,dyadicMesh]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg (d:ℝ))]
  | succ n ih =>
    have h1 := ih t (d/2)
    have h2 := ih (t+d/2) (d/2)
    have ht : t+d/2+d/2=t+d := by ring
    have ha : (γ t:ℝ)≤γ (t+d/2) := by exact_mod_cast hγ (le_add_of_nonneg_right (show 0≤d/2 from zero_le))
    rw [ht] at h2
    rw [dyadic_penalty_succ,dyadic_penalty_succ,dyadicMesh_succ]
    have hdm : 0≤(dyadicMesh (d/2) n:ℝ) := (dyadicMesh (d/2) n).coe_nonneg
    have hu : ((t:ℝ)+d/2)*(dyadicMesh (d/2) n:ℝ)*((γ (t+d/2):ℝ)-γ t)/2≤
        ((t:ℝ)+d)*(dyadicMesh (d/2) n:ℝ)*((γ (t+d/2):ℝ)-γ t)/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr ha)
      exact mul_le_mul_of_nonneg_right (by linarith [d.coe_nonneg]) hdm
    have he : (t:ℝ)+(d/2:ℝ≥0)+(d/2:ℝ≥0)=(t:ℝ)+d := by change (t:ℝ)+d/2+d/2=t+d; ring
    have hc : (t+d/2:ℝ≥0)=(t:ℝ)+d/2 := rfl
    rw [hc] at h2
    rw [show ((d/2:ℝ≥0):ℝ)=(d:ℝ)/2 from rfl] at h1 h2
    have he' : (t:ℝ)+d/2+d/2=t+d := by ring
    rw [he'] at h2
    linarith

lemma dyadic_penalty_error {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ}
    (hb : ∀ s,(γ s:ℝ)≤β) (t d : ℝ≥0) (n : ℕ) :
    |coefficientPenalty γ t d-penalty t (dyadicSchedule γ false t d n)|≤
      ((t:ℝ)+d)*(dyadicMesh d n:ℝ)*β/2 := by
  have hbounds := dyadic_penalty_bounds hγ t d n
  rw [abs_of_nonneg (sub_nonneg.mpr hbounds.1)]
  have he := dyadic_penalty_difference hγ t d n
  have hc : (γ (t+d):ℝ)-γ t≤β := by linarith [hb (t+d),(γ t).coe_nonneg]
  have hd : ((t:ℝ)+d)*(dyadicMesh d n:ℝ)*((γ (t+d):ℝ)-γ t)/2≤
      ((t:ℝ)+d)*(dyadicMesh d n:ℝ)*β/2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_left hc (mul_nonneg (add_nonneg t.coe_nonneg d.coe_nonneg) (dyadicMesh d n).coe_nonneg)
  linarith

lemma dyadic_penalty_tendsto {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ}
    (hb : ∀ s,(γ s:ℝ)≤β) (t d : ℝ≥0) :
    Tendsto (fun n => penalty t (dyadicSchedule γ false t d n)) atTop (𝓝 (coefficientPenalty γ t d)) := by
  have herr : Tendsto (fun n => ((t:ℝ)+d)*(dyadicMesh d n:ℝ)*β/2) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,zero_mul,zero_div] using (((dyadicMesh_tendsto d).const_mul ((t:ℝ)+d)).mul_const β).div_const 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using tendsto_const_nhds.sub herr) tendsto_const_nhds
  · intro n
    have hh := (abs_le.mp (dyadic_penalty_error hγ hb t d n)).2
    linarith
  · exact fun n => (dyadic_penalty_bounds hγ t d n).1

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

 

def orderParameterFunctional (β : ℝ) (γ : ℝ≥0 → ℝ≥0) : ℝ :=
  dyadicEvolution γ 0 1 (terminal β) 0-coefficientPenalty γ 0 1

lemma dyadic_admissible {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ}
    (hb : ∀ s,(γ s:ℝ)≤β) (n : ℕ) : Admissible β (dyadicSchedule γ false 0 1 n) := by
  refine ⟨dyadicSchedule_width γ false 0 1 n,?_,?_⟩
  · rw [dyadicSchedule_eq_uniform]
    apply List.pairwise_ofFn.mpr
    intro i j hij
    apply hγ
    gcongr
    exact_mod_cast hij.le
  · rw [dyadicSchedule_eq_uniform]
    intro l hl
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hl
    exact hb _

lemma dyadic_functional_tendsto {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ}
    (hβ : 0<β) (hb : ∀ s,(γ s:ℝ)≤β) :
    Tendsto (fun n => functional β (dyadicSchedule γ false 0 1 n)) atTop
      (𝓝 (orderParameterFunctional β γ)) := by
  have hr := dyadic_low_tendsto (terminal_lipschitz hβ) hγ 0 1 0
  have hp := dyadic_penalty_tendsto hγ hb 0 1
  simpa only [functional,recursion_eq_evolve,orderParameterFunctional,NNReal.coe_zero] using hr.sub hp

lemma limitingFreeEnergy_le_orderParameterFunctional {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ)
    {β : ℝ} (hβ : 0<β) (hb : ∀ s,(γ s:ℝ)≤β) :
    SKQAOA.limitingFreeEnergy β≤orderParameterFunctional β γ := by
  apply ge_of_tendsto (dyadic_functional_tendsto hγ hβ hb)
  exact Eventually.of_forall fun n => by
    simpa only [Real.coe_toNNReal β hβ.le] using
      ParisiGuerra.limitingFreeEnergy_le_functional (Real.toNNReal β) (Real.toNNReal_pos.mpr hβ)
        (dyadicSchedule γ false 0 1 n) (by simpa only [Real.coe_toNNReal β hβ.le] using dyadic_admissible hγ hb n)

end ParisiFinite
namespace SKCavity
open ParisiFinite SKQAOA

def overlapCDFCoefficient (μ : ProbabilityMeasure OverlapArray) (β : ℝ≥0) (s : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (overlapDiscount μ s)*β

lemma overlapCDFCoefficient_mono (μ : ProbabilityMeasure OverlapArray) (β : ℝ≥0) :
    Monotone (overlapCDFCoefficient μ β) := by
  intro x y hxy
  exact mul_le_mul_of_nonneg_right (Real.toNNReal_mono (overlapDiscount_mono μ (by exact_mod_cast hxy))) (by positivity)

lemma overlapCDFCoefficient_bound (μ : ProbabilityMeasure OverlapArray) (β : ℝ≥0) (s : ℝ≥0) :
    (overlapCDFCoefficient μ β s:ℝ)≤β := by
  change (Real.toNNReal (overlapDiscount μ s):ℝ)*(β:ℝ)≤β
  rw [Real.coe_toNNReal (overlapDiscount μ s) (show 0≤overlapDiscount μ s from measureReal_nonneg)]
  nlinarith [overlapDiscount_le_one μ s,β.coe_nonneg]

lemma dyadic_CDF_schedule (μ : ProbabilityMeasure OverlapArray) (β : ℝ≥0) (n : ℕ) :
    dyadicSchedule (overlapCDFCoefficient μ β) false 0 1 n=gridSchedule μ β (2^n-1) := by
  have hN : 1≤2^n := one_le_pow₀ (by norm_num)
  have hdim : 2^n-1+1=2^n := Nat.sub_add_cancel hN
  rw [dyadicSchedule_eq_uniform,← hdim]
  unfold uniformLower gridSchedule
  apply congrArg List.ofFn
  funext k
  apply Prod.ext
  · simp only [zero_add,one_mul,overlapCDFCoefficient,cavityGrid,Fin.cons_succ]
    rfl
  · rfl

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

abbrev OrderPoint := Set.Icc (0:ℝ) 1

 
def measureCoefficient (ρ : ProbabilityMeasure OrderPoint) (β : ℝ≥0) (s : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal ((ρ:Measure OrderPoint).real {x | (x:ℝ) ≤ s})*β

def measureFunctional (β : ℝ≥0) (ρ : ProbabilityMeasure OrderPoint) : ℝ :=
  orderParameterFunctional β (measureCoefficient ρ β)

lemma measureCoefficient_mono (ρ : ProbabilityMeasure OrderPoint) (β : ℝ≥0) :
    Monotone (measureCoefficient ρ β) := by
  intro x y hxy
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.toNNReal_mono
  exact measureReal_mono (by
    intro z hz
    change (z:ℝ) ≤ (x:ℝ) at hz
    change (z:ℝ) ≤ (y:ℝ)
    exact hz.trans (NNReal.coe_le_coe.mpr hxy))

lemma measureCoefficient_bound (ρ : ProbabilityMeasure OrderPoint) (β : ℝ≥0) (s : ℝ≥0) :
    (measureCoefficient ρ β s:ℝ) ≤ β := by
  change (Real.toNNReal ((ρ:Measure OrderPoint).real {x | (x:ℝ) ≤ s}):ℝ)*(β:ℝ) ≤ β
  rw [Real.coe_toNNReal _ measureReal_nonneg]
  have hh : (ρ:Measure OrderPoint).real {x | (x:ℝ) ≤ s} ≤ 1 := measureReal_le_one
  nlinarith [β.coe_nonneg]

lemma pressure_le_measureFunctional {β : ℝ≥0} (hβ : 0<β) (ρ : ProbabilityMeasure OrderPoint) :
    SKQAOA.limitingFreeEnergy β ≤ measureFunctional β ρ :=
  limitingFreeEnergy_le_orderParameterFunctional (measureCoefficient_mono ρ β) hβ (measureCoefficient_bound ρ β)

end ParisiFinite
namespace SKCavity
open ParisiFinite SKQAOA

def orderPointOfArray (R : OverlapArray) : OrderPoint :=
  ⟨max 0 (R 0 1:ℝ),le_max_left _ _,max_le (by norm_num) (R 0 1).property.2⟩

lemma orderPointOfArray_continuous : Continuous orderPointOfArray := by
  apply Continuous.subtype_mk
  exact continuous_const.max (continuous_subtype_val.comp (continuous_apply 1 |>.comp (continuous_apply 0)))

def orderParameterLaw (μ : ProbabilityMeasure OverlapArray) : ProbabilityMeasure OrderPoint :=
  μ.map orderPointOfArray

lemma orderParameterLaw_coefficient (μ : ProbabilityMeasure OverlapArray) (β : ℝ≥0) :
    measureCoefficient (orderParameterLaw μ) β=overlapCDFCoefficient μ β := by
  funext s
  unfold measureCoefficient overlapCDFCoefficient
  congr 2
  unfold orderParameterLaw overlapDiscount entryLaw
  simp only [Measure.real]
  rw [ProbabilityMeasure.toMeasure_map,Measure.map_apply orderPointOfArray_continuous.measurable
    (by measurability : MeasurableSet {x : OrderPoint | (x:ℝ) ≤ s}),
    Measure.map_apply (by fun_prop : Measurable (fun R : OverlapArray => R 0 1))
      (by measurability : MeasurableSet {x : OverlapEntry | (x:ℝ) ≤ s})]
  congr 2
  ext R
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,orderPointOfArray,max_le_iff]
  exact and_iff_right s.coe_nonneg

lemma dyadic_indices_tendsto : Tendsto (fun n : ℕ => 2^n-1) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro n
  change n ≤ 2^n-1
  have hn : n<2^n := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  omega

 

theorem exists_measure_pressure_equality {β : ℝ≥0} (hβ : 0<β) :
    ∃ ρ : ProbabilityMeasure OrderPoint,measureFunctional β ρ=limitingFreeEnergy β := by
  have hb : (0:ℝ)<β := hβ
  obtain ⟨μ,v,hG,hgg,hex,hu,hv,hbound⟩ := exists_scalar_ultrametric_cavity hb
  let γ := overlapCDFCoefficient μ β
  have ht := dyadic_functional_tendsto (overlapCDFCoefficient_mono μ β) hb (overlapCDFCoefficient_bound μ β)
  have hupper (n : ℕ) : functional β (dyadicSchedule γ false 0 1 n) ≤ 
      limitingFreeEnergy β+(β:ℝ)*Real.pi/(2^n:ℕ) := by
    have hh := (abs_le.mp (gridFunctional_cavity_error hG hgg hu hex hb hv (2^n-1))).1
    have he : 2^n-1+1=2^n := Nat.sub_add_cancel (one_le_pow₀ (by norm_num))
    have hβeq : Real.toNNReal (β:ℝ)=β := Real.toNNReal_coe
    rw [hβeq,he] at hh
    change -((β:ℝ)^2*Real.pi/(2^n:ℕ)) ≤ v-(β:ℝ)*functional β (gridSchedule μ β (2^n-1)) at hh
    rw [dyadic_CDF_schedule]
    have heq : (β:ℝ)^2*Real.pi/(2^n:ℕ)=(β:ℝ)*((β:ℝ)*Real.pi/(2^n:ℕ)) := by ring
    rw [heq] at hh
    nlinarith
  have herr : Tendsto (fun n : ℕ => (β:ℝ)*Real.pi/(2^n:ℕ)) atTop (𝓝 (0:ℝ)) := by
    have hh := (dyadicMesh_tendsto 1).const_mul ((β:ℝ)*Real.pi)
    change Tendsto (fun n : ℕ => (β:ℝ)*Real.pi*(1/(2:ℝ)^n)) atTop (𝓝 ((β:ℝ)*Real.pi*0)) at hh
    simpa only [Nat.cast_pow,Nat.cast_ofNat,mul_zero,mul_one_div] using hh
  have hlim : orderParameterFunctional β γ ≤ limitingFreeEnergy β :=
    le_of_tendsto_of_tendsto ht (by simpa only [add_zero] using tendsto_const_nhds.add herr)
      (Eventually.of_forall hupper)
  refine ⟨orderParameterLaw μ,le_antisymm ?_ (pressure_le_measureFunctional hβ _)⟩
  simpa only [measureFunctional,orderParameterLaw_coefficient,γ] using hlim

end SKCavity
namespace ParisiFinite

 

def IsMinimizingParisiMeasure (β : ℝ≥0) (ρ : ProbabilityMeasure OrderPoint) : Prop :=
  ∀ ν : ProbabilityMeasure OrderPoint,measureFunctional β ρ ≤ measureFunctional β ν

 

theorem exists_minimizing_Parisi_measure {β : ℝ≥0} (hβ : 0<β) :
    ∃ ρ : ProbabilityMeasure OrderPoint,IsMinimizingParisiMeasure β ρ ∧
      measureFunctional β ρ=SKQAOA.limitingFreeEnergy β := by
  obtain ⟨ρ,hρ⟩ := SKCavity.exists_measure_pressure_equality hβ
  exact ⟨ρ,(fun ν => hρ.le.trans (pressure_le_measureFunctional hβ ν)),hρ⟩

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

lemma tiltedMean_const {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a s x c : ℝ) : tiltedMean a s f (fun _ => c) x=c := by
  unfold tiltedMean expMoment expMass
  simp only [integral_mul_const]
  exact mul_div_cancel_left₀ c (expMass_pos hf a s x).ne'

lemma tiltedMean_nonneg {f g : ℝ → ℝ} (hg : ∀ x,0 ≤ g x) (a s x : ℝ) :
    0 ≤ tiltedMean a s f g x := by
  unfold tiltedMean expMoment expMass
  exact div_nonneg (integral_nonneg fun z => mul_nonneg (Real.exp_pos _).le (hg _))
    (integral_nonneg fun _ => (Real.exp_pos _).le)

lemma tiltedMean_mono {L : ℝ≥0} {f g h : ℝ → ℝ}
    (hf : LipschitzWith L f) (hg : Continuous g) (hh : Continuous h) {M N : ℝ}
    (hM : ∀ x,|g x| ≤ M) (hN : ∀ x,|h x| ≤ N) (hgh : ∀ x,g x ≤ h x)
    (a s x : ℝ) : tiltedMean a s f g x ≤ tiltedMean a s f h x := by
  apply div_le_div_of_nonneg_right _ (expMass_pos hf a s x).le
  exact integral_mono (integrable_exp_weight hf hg hM a s x)
    (integrable_exp_weight hf hh hN a s x) (fun z => mul_le_mul_of_nonneg_left (hgh _) (Real.exp_pos _).le)

lemma tiltedMean_variance_nonneg {L M : ℝ≥0} {f g : ℝ → ℝ}
    (hf : LipschitzWith L f) (hg : Continuous g) (hM : ∀ x,|g x| ≤ M) (a s x : ℝ) :
    (tiltedMean a s f g x)^2 ≤ tiltedMean a s f (fun y => g y^2) x := by
  let c := tiltedMean a s f g x
  have hgi : Integrable (fun z => Real.exp (a*f (x+s*z))*g (x+s*z)) (gaussianReal 0 1) :=
    integrable_exp_weight hf hg hM a s x
  have hgs : Integrable (fun z => Real.exp (a*f (x+s*z))*g (x+s*z)^2) (gaussianReal 0 1) :=
    integrable_exp_weight hf (by fun_prop) (sq_bound hM) a s x
  have hi : 0 ≤ ∫ z : ℝ,Real.exp (a*f (x+s*z))*(g (x+s*z)-c)^2 ∂gaussianReal 0 1 := integral_nonneg
    (fun z => mul_nonneg (Real.exp_pos (a*f (x+s*z))).le (sq_nonneg (g (x+s*z)-c)))
  have he (z : ℝ) : Real.exp (a*f (x+s*z))*(g (x+s*z)-c)^2 =
      Real.exp (a*f (x+s*z))*g (x+s*z)^2 -
        (2*c)*(Real.exp (a*f (x+s*z))*g (x+s*z)) + c^2*Real.exp (a*f (x+s*z)) := by ring
  simp_rw [he] at hi
  have hadd := integral_add (hgs.sub (hgi.const_mul (2*c))) ((integrable_exp_shift hf a x s).const_mul (c^2))
  have hsub := integral_sub hgs (hgi.const_mul (2*c))
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd,hsub,integral_const_mul,integral_const_mul] at hi
  have hp := expMass_pos hf a s x
  change 0 ≤ expMoment a s f (fun y => g y^2) x - 2*c*expMoment a s f g x + c^2*expMass a s f x at hi
  have hc : expMoment a s f g x=c*expMass a s f x := by
    dsimp [c,tiltedMean]; exact (div_mul_cancel₀ _ hp.ne').symm
  rw [hc] at hi
  dsimp [tiltedMean]
  apply (le_div_iff₀ hp).mpr
  change c^2*expMass a s f x ≤ _
  nlinarith

 

def HasParisiCurvature (β : ℝ≥0) (f : SmoothField) : Prop :=
  f.bound1=1 ∧ ∀ x, 0 ≤ f.d2 x ∧ f.d2 x ≤ (β:ℝ)*(1-f.d1 x^2)

lemma terminal_hasParisiCurvature (β : ℝ≥0) (hβ : 0<β) :
    HasParisiCurvature β (terminalField β hβ) := by
  refine ⟨rfl,fun x => ⟨by dsimp [terminalField]; positivity,?_⟩⟩
  change (β:ℝ)/Real.cosh ((β:ℝ)*x)^2 ≤ (β:ℝ)*(1-Real.tanh ((β:ℝ)*x)^2)
  have hh := Real.cosh_sq_sub_sinh_sq ((β:ℝ)*x)
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc := (Real.cosh_pos ((β:ℝ)*x)).ne'
  field_simp
  nlinarith [β.coe_nonneg]

lemma transform_hasParisiCurvature {β : ℝ≥0} {f : SmoothField}
    (hf : HasParisiCurvature β f) {a : ℝ} (ha : 0 ≤ a) (hab : a ≤ β) (s : ℝ) :
    HasParisiCurvature β (f.transform a s) := by
  refine ⟨hf.1,fun x => ?_⟩
  have hv := tiltedMean_variance_nonneg f.lipschitz f.continuousD1 f.normD1 a s x
  have hn := tiltedMean_nonneg (f := f.val) (fun y => (hf.2 y).1) a s x
  have h1 : ∀ y,|f.d1 y| ≤ (1:ℝ) := by simpa only [hf.1,NNReal.coe_one] using f.normD1
  have hsum : ∀ y,|f.d2 y+(β:ℝ)*f.d1 y^2| ≤ (f.bound2:ℝ)+(β:ℝ) := by
    intro y
    apply (abs_add_le _ _).trans
    have hh := sq_bound (L := 1) h1 y
    norm_num only [NNReal.coe_one,one_pow] at hh
    rw [abs_mul,abs_of_nonneg β.coe_nonneg]
    nlinarith [f.normD2 y,β.coe_nonneg]
  have hm := tiltedMean_mono f.lipschitz
    (g := fun y => f.d2 y+(β:ℝ)*f.d1 y^2) (h := fun _ => (β:ℝ))
    (by have h₂ := f.continuousD2; have h₁ := f.continuousD1; fun_prop)
    continuous_const hsum (by intro; exact abs_of_nonneg β.coe_nonneg |>.le)
    (fun y => by have hh := (hf.2 y).2; linarith) a s x
  rw [tiltedMean_add f.lipschitz f.continuousD2
    (by have hc := f.continuousD1; fun_prop) f.normD2
    (fun y => by rw [abs_mul,abs_of_nonneg β.coe_nonneg]; exact mul_le_mul_of_nonneg_left (sq_bound f.normD1 y) β.coe_nonneg),
    tiltedMean_const_mul,tiltedMean_const f.lipschitz] at hm
  change 0 ≤ tiltedMean a s f.val f.d2 x + a*(tiltedMean a s f.val (fun y => f.d1 y^2) x-(tiltedMean a s f.val f.d1 x)^2) ∧
    tiltedMean a s f.val f.d2 x + a*(tiltedMean a s f.val (fun y => f.d1 y^2) x-(tiltedMean a s f.val f.d1 x)^2) ≤
      (β:ℝ)*(1-(tiltedMean a s f.val f.d1 x)^2)
  constructor
  · exact add_nonneg hn (mul_nonneg ha (sub_nonneg.mpr hv))
  · nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hv)]

lemma smoothRecursion_hasParisiCurvature (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (ha : ∀ l∈ls,l.1 ≤ β) : HasParisiCurvature β (smoothRecursion β hβ ls) := by
  induction ls with
  | nil => exact terminal_hasParisiCurvature β hβ
  | cons l ls ih =>
    exact transform_hasParisiCurvature (ih (fun k hk => ha k (List.mem_cons_of_mem _ hk)))
      l.1.coe_nonneg (by exact_mod_cast ha l (List.mem_cons_self)) _

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

lemma curvature_abs_d2 {β : ℝ≥0} {f : SmoothField} (hf : HasParisiCurvature β f) (x : ℝ) :
    |f.d2 x| ≤ β := by
  rw [abs_of_nonneg (hf.2 x).1]
  have hh := (hf.2 x).2
  nlinarith [mul_nonneg β.coe_nonneg (sq_nonneg (f.d1 x))]

lemma curvature_gradient_lipschitz {β : ℝ≥0} {f : SmoothField} (hf : HasParisiCurvature β f) :
    LipschitzWith β f.d1 := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (f.hasD2 x).differentiableAt)
  intro x
  rw [(f.hasD2 x).deriv]
  exact_mod_cast curvature_abs_d2 hf x

lemma curvature_taylor_error {β : ℝ≥0} {f : SmoothField} (hf : HasParisiCurvature β f)
    (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    |f.val (x+h)-f.val x-h*f.d1 x| ≤ (β:ℝ)*h^2 := by
  let r (y : ℝ) := f.val y-f.val x-(y-x)*f.d1 x
  have hd (y : ℝ) : HasDerivAt r (f.d1 y-f.d1 x) y := by
    convert (f.hasD1 y |>.sub_const (f.val x)).sub
      (((hasDerivAt_id y).sub_const x).mul_const (f.d1 x)) using 1 <;>
      first | rfl | simp only [one_mul]
  have hb (y : ℝ) (hy : y∈Set.Ico x (x+h)) : ‖f.d1 y-f.d1 x‖ ≤ (β:ℝ)*h := by
    have hl := (curvature_gradient_lipschitz hf).dist_le_mul y x
    rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hy.1)] at hl
    simpa only [Real.norm_eq_abs] using hl.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) β.coe_nonneg)
  have ht := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y (_ : y∈Set.Icc x (x+h)) => (hd y).hasDerivWithinAt) hb (x+h) ⟨by linarith,le_rfl⟩
  simpa only [r,sub_self,zero_mul,sub_zero,add_sub_cancel_left,Real.norm_eq_abs,pow_two,mul_assoc] using ht

 

lemma curvature_derivative_stability {β : ℝ≥0} {f g : SmoothField}
    (hf : HasParisiCurvature β f) (hg : HasParisiCurvature β g)
    {ε h : ℝ} (hh : 0 ≤ h) (he : ∀ y,|f.val y-g.val y| ≤ ε) (x : ℝ) :
    h*|f.d1 x-g.d1 x| ≤ 2*ε+2*(β:ℝ)*h^2 := by
  have hferr := abs_le.mp (curvature_taylor_error hf x hh)
  have hgerr := abs_le.mp (curvature_taylor_error hg x hh)
  have hx := abs_le.mp (he x)
  have hx' := abs_le.mp (he (x+h))
  have ha : h*|f.d1 x-g.d1 x|=|h*(f.d1 x-g.d1 x)| := by rw [abs_mul,abs_of_nonneg hh]
  rw [ha,abs_le]
  constructor <;> nlinarith

lemma uniform_derivative_cauchy {β : ℝ≥0} {F : ℕ → SmoothField} {g : ℝ → ℝ}
    (hF : ∀ n,HasParisiCurvature β (F n))
    (ht : TendstoUniformly (fun n => (F n).val) g atTop) :
    UniformCauchySeqOn (fun n => (F n).d1) atTop Set.univ := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  let h := ε/(8*((β:ℝ)+1))
  have hh : 0<h := by dsimp [h]; positivity
  have hsmall : 2*(β:ℝ)*h ≤ ε/4 := by
    dsimp [h]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    field_simp
    nlinarith [β.coe_nonneg]
  obtain ⟨N,hN⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp ht (ε*h/8) (by positivity))
  refine ⟨N,fun m hm n hn x _ => ?_⟩
  have hd : ∀ y,|(F m).val y-(F n).val y| ≤ 2*(ε*h/8) := by
    intro y
    have h₁ := hN m hm y
    have h₂ := hN n hn y
    rw [Real.dist_eq] at h₁ h₂
    calc
      _ ≤ |(F m).val y-g y|+|g y-(F n).val y| := abs_sub_le _ _ _
      _ ≤ 2*(ε*h/8) := by rw [abs_sub_comm] at h₁; linarith
  have hbnd := curvature_derivative_stability (hF m) (hF n) hh.le hd x
  rw [Real.dist_eq]
  have hmul := mul_le_mul_of_nonneg_right hsmall hh.le
  nlinarith

lemma exists_uniform_derivative_limit {β : ℝ≥0} {F : ℕ → SmoothField} {g : ℝ → ℝ}
    (hF : ∀ n,HasParisiCurvature β (F n))
    (ht : TendstoUniformly (fun n => (F n).val) g atTop) :
    ∃ g' : ℝ → ℝ,TendstoUniformly (fun n => (F n).d1) g' atTop ∧
      (∀ x,HasDerivAt g (g' x) x) ∧ LipschitzWith β g' ∧ (∀ x,|g' x| ≤ 1) := by
  have hc := uniform_derivative_cauchy hF ht
  choose g' hg' using fun x : ℝ => cauchySeq_tendsto_of_complete (hc.cauchySeq (Set.mem_univ x))
  have hu : TendstoUniformly (fun n => (F n).d1) g' atTop := by
    rw [← tendstoUniformlyOn_univ]
    exact hc.tendstoUniformlyOn_of_tendsto (fun x _ => hg' x)
  refine ⟨g',hu,fun x => hasDerivAt_of_tendstoUniformly hu (Eventually.of_forall (fun n y => (F n).hasD1 y)) (fun y => ht.tendsto_at y) x,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    apply le_of_tendsto ((hg' x).dist (hg' y))
    exact Eventually.of_forall fun n => (curvature_gradient_lipschitz (hF n)).dist_le_mul x y
  · intro x
    apply le_of_tendsto (hg' x |>.abs)
    exact Eventually.of_forall fun n => by simpa only [(hF n).1,NNReal.coe_one] using (F n).normD1 x

end ParisiFinite

end

end OAI
