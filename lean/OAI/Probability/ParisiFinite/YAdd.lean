import Mathlib
import OAI.Probability.ParisiFinite.BalancedConeEqForest

namespace OAI

/-! Y Add. -/

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
open scoped Topology
open Filter

namespace CompactSeedControl
variable {S : Type*} [TopologicalSpace S] [CompactSpace S] [Nonempty S]
local instance yAddSpinFieldNormedAlgebraRat : NormedAlgebra ℚ (SpinField S) := NormedAlgebra.restrictScalars ℚ ℝ (SpinField S)

omit [CompactSpace S] [Nonempty S] in
@[simp] theorem Y_add (f g : C(S,ℝ)) : Y (f+g)=Y f+Y g := by
  apply ContinuousMap.ext
  intro s
  change (f s+g s) • (⟨0,0,1,0⟩ : Quaternion ℝ) = _
  exact add_smul (f s) (g s) _
omit [CompactSpace S] [Nonempty S] in
@[simp] theorem Z_add (f g : C(S,ℝ)) : Z (f+g)=Z f+Z g := by
  apply ContinuousMap.ext
  intro s
  change (f s+g s) • (⟨0,1,0,0⟩ : Quaternion ℝ) = _
  exact add_smul (f s) (g s) _
omit [CompactSpace S] [Nonempty S] in
@[simp] theorem Y_zero : Y (0 : C(S,ℝ))=0 := by
  apply ContinuousMap.ext
  intro s
  change (0:ℝ) • (⟨0,0,1,0⟩ : Quaternion ℝ)=0
  exact zero_smul _ _
omit [CompactSpace S] [Nonempty S] in
@[simp] theorem Z_zero : Z (0 : C(S,ℝ))=0 := by
  apply ContinuousMap.ext
  intro s
  change (0:ℝ) • (⟨0,1,0,0⟩ : Quaternion ℝ)=0
  exact zero_smul _ _

def oddEval (s : C(S,ℝ)) (P : Polynomial ℝ) : C(S,ℝ) :=
  (1/2:ℝ) • (P.aeval s-P.aeval (-s))

omit [CompactSpace S] [Nonempty S] in
@[simp] theorem oddEval_add (s : C(S,ℝ)) (P Q : Polynomial ℝ) :
    oddEval s (P+Q)=oddEval s P+oddEval s Q := by
  unfold oddEval
  simp only [map_add]
  module

omit [CompactSpace S] [Nonempty S] in
@[simp] theorem oddEval_monomial_even (s : C(S,ℝ)) (k : ℕ) (a : ℝ) :
    oddEval s (Polynomial.monomial (2*k) a)=0 := by
  ext t
  simp [oddEval,Polynomial.aeval_monomial,pow_mul]

omit [CompactSpace S] [Nonempty S] in
@[simp] theorem oddEval_monomial_odd (s : C(S,ℝ)) (k : ℕ) (a : ℝ) :
    oddEval s (Polynomial.monomial (2*k+1) a)=a • (s*(s^2)^k) := by
  ext t
  simp [oddEval,Polynomial.aeval_monomial,pow_succ,pow_mul]
  ring

 

theorem odd_polynomial_mem (s : C(S,ℝ)) (P : Polynomial ℝ) :
    Y (oddEval s P)∈available s ∧ Z (oddEval s P)∈available s := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [oddEval_add,Y_add,Z_add]
    exact ⟨(available s).add_mem hP.1 hQ.1,(available s).add_mem hP.2 hQ.2⟩
  | monomial k a =>
    obtain ⟨m,hm|hm⟩ := Nat.even_or_odd' k
    · subst k
      simp
    · subst k
      rw [oddEval_monomial_odd,Y_smul,Z_smul]
      exact ⟨(available s).smul_mem a (Y_seed_mul_mem s _ (X_even_power_mem s m)),
        (available s).smul_mem a (Z_seed_mul_mem s _ (X_even_power_mem s m))⟩

 
theorem odd_continuous_mem (s : C(S,ℝ)) (f : C(ℝ,ℝ)) (hf : Function.Odd f) :
    Y (f.comp s)∈available s ∧ Z (f.comp s)∈available s := by
  let I := Set.Icc (-‖s‖) ‖s‖
  let η : C(S,I) := ⟨fun t => ⟨s t,⟨s.neg_norm_le_apply t,s.apply_le_norm t⟩⟩,
    by fun_prop⟩
  let ν : C(S,I) := ⟨fun t => ⟨-s t,by
    constructor <;> linarith [s.neg_norm_le_apply t,s.apply_le_norm t]⟩,
    by fun_prop⟩
  let T (g : C(I,ℝ)) : C(S,ℝ) := (1/2:ℝ) • (g.comp η-g.comp ν)
  have hT : Continuous T := by
    change Continuous (fun g : C(I,ℝ) => (1/2:ℝ) • (g.comp η-g.comp ν))
    exact (continuous_const : Continuous (fun _ : C(I,ℝ) => (1/2:ℝ))).smul ((ContinuousMap.compRightAlgHom_continuous ℝ ℝ η).sub
      (ContinuousMap.compRightAlgHom_continuous ℝ ℝ ν))
  have hz : IsClosed {g : C(I,ℝ) | Y (T g)∈available s ∧ Z (T g)∈available s} :=
    ((RawPulseControl.closed_directions (generator s) (generator_skew s)).preimage
      (continuous_Y.comp hT)).inter
    ((RawPulseControl.closed_directions (generator s) (generator_skew s)).preimage
      (continuous_Z.comp hT))
  have hp : (polynomialFunctions I : Set C(I,ℝ)) ⊆
      {g : C(I,ℝ) | Y (T g)∈available s ∧ Z (T g)∈available s} := by
    intro g hg
    rw [polynomialFunctions_coe] at hg
    obtain ⟨P,rfl⟩ := hg
    have he : T (P.toContinuousMapOn I)=oddEval s P := by
      ext t
      simp [T,η,ν,oddEval,Polynomial.toContinuousMapOn,Polynomial.toContinuousMap]
    change Y (T (P.toContinuousMapOn I))∈available s ∧ Z (T (P.toContinuousMapOn I))∈available s
    rw [he]
    exact odd_polynomial_mem s P
  have ht : f.restrict I ∈ closure (polynomialFunctions I : Set C(I,ℝ)) :=
    continuousMap_mem_polynomialFunctions_closure (-‖s‖) ‖s‖ _
  have hh := closure_minimal hp hz ht
  have he : T (f.restrict I)=f.comp s := by
    ext t
    change (1/2:ℝ)*(f (s t)-f (-s t))=f (s t)
    rw [hf]
    ring
  change Y (T (f.restrict I))∈available s ∧ Z (T (f.restrict I))∈available s at hh
  rwa [he] at hh

 
theorem odd_continuous_pulse_approximation (s : C(S,ℝ)) (f : C(ℝ,ℝ))
    (hf : Function.Odd f) (t : ℝ) {ε : ℝ} (hε : 0<ε) :
    (∃w : List (Bool×ℝ),‖PulseControl.pulseValue (generator s) w-
      NormedSpace.exp (t•Y (f.comp s))‖<ε) ∧
    (∃w : List (Bool×ℝ),‖PulseControl.pulseValue (generator s) w-
      NormedSpace.exp (t•Z (f.comp s))‖<ε) :=
  ⟨RawPulseControl.approximate (generator s) (generator_skew s) (odd_continuous_mem s f hf).1 t hε,
   RawPulseControl.approximate (generator s) (generator_skew s) (odd_continuous_mem s f hf).2 t hε⟩

end CompactSeedControl

 

open scoped Topology
open Filter

namespace CompactSeedControl
local instance yAddQuaternionNormedAlgebraRatOne : NormedAlgebra ℚ (Quaternion ℝ) := NormedAlgebra.restrictScalars ℚ ℝ (Quaternion ℝ)

def axisX : Quaternion ℝ := ⟨0,0,0,1⟩
def axisY : Quaternion ℝ := ⟨0,0,1,0⟩
def axisZ : Quaternion ℝ := ⟨0,1,0,0⟩

theorem axisX_skew : axisX∈skewAdjoint (Quaternion ℝ) := by
  rw [skewAdjoint.mem_iff]
  exact Quaternion.star_eq_neg.mpr rfl
theorem axisY_skew : axisY∈skewAdjoint (Quaternion ℝ) := by
  rw [skewAdjoint.mem_iff]
  exact Quaternion.star_eq_neg.mpr rfl
theorem axisZ_skew : axisZ∈skewAdjoint (Quaternion ℝ) := by
  rw [skewAdjoint.mem_iff]
  exact Quaternion.star_eq_neg.mpr rfl

def rawGenerator (r : ℝ) (a : Bool) : Quaternion ℝ := if a then r•axisZ else axisX

theorem rawGenerator_skew (r : ℝ) (a : Bool) : rawGenerator r a∈skewAdjoint (Quaternion ℝ) := by
  cases a
  · exact axisX_skew
  · exact skewAdjoint.smul_mem r axisZ_skew

theorem rawGenerator_continuous (a : Bool) : Continuous (fun r => rawGenerator r a) := by
  cases a
  · exact continuous_const
  · exact continuous_id.smul continuous_const

 
def localWord (w : List (Bool×ℝ)) (s : ℝ) : Quaternion ℝ :=
  PulseControl.pulseValue (rawGenerator s) w

theorem localWord_unitary (w : List (Bool×ℝ)) (s : ℝ) : localWord w s∈unitary (Quaternion ℝ) :=
  RawPulseControl.words_unitary (rawGenerator s) (rawGenerator_skew s) ⟨w,rfl⟩

theorem localWord_continuous (w : List (Bool×ℝ)) : Continuous (localWord w) := by
  induction w with
  | nil => exact continuous_const
  | cons p w ih =>
    change Continuous (fun r => NormedSpace.exp (p.2 • rawGenerator r p.1)*localWord w r)
    exact (NormedSpace.exp_continuous.comp
      ((continuous_const : Continuous (fun _ : ℝ => p.2)).smul (rawGenerator_continuous p.1))).mul ih

section Compact
variable {S : Type*} [TopologicalSpace S] [CompactSpace S] [Nonempty S]
local instance yAddCompactSpinFieldNormedAlgebraRat : NormedAlgebra ℚ (SpinField S) := NormedAlgebra.restrictScalars ℚ ℝ (SpinField S)

def fieldEval (s : S) : SpinField S →+* Quaternion ℝ where
  toFun f := f s
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

omit [CompactSpace S] [Nonempty S] in
theorem fieldEval_continuous (s : S) : Continuous (fieldEval s) := by
  exact continuous_eval_const s

omit [Nonempty S] in
@[simp] theorem field_exp_apply (f : SpinField S) (s : S) :
    (NormedSpace.exp f) s=NormedSpace.exp (f s) :=
  NormedSpace.map_exp (fieldEval s) (fieldEval_continuous s) f

omit [Nonempty S] in
@[simp] theorem field_pulse_apply (s : C(S,ℝ)) (w : List (Bool×ℝ)) (r : S) :
    PulseControl.pulseValue (generator s) w r=localWord w (s r) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    change (NormedSpace.exp (p.2 • generator s p.1)) r *
      PulseControl.pulseValue (generator s) w r =
      NormedSpace.exp (p.2 • rawGenerator (s r) p.1)*localWord w (s r)
    rw [field_exp_apply,ih]
    congr 2
    cases p.1 <;> simp only [generator,rawGenerator,ContinuousMap.smul_apply]
    · change p.2 • ((1:ℝ)•axisX)=p.2•axisX
      rw [one_smul]
    · rfl

end Compact

 

theorem even_localWord_compact (f : C(ℝ,ℝ)) (hf : Function.Even f) (t R : ℝ)
    (hR : 0≤R) {ε : ℝ} (hε : 0<ε) :
    ∃w : List (Bool×ℝ),∀r : ℝ,|r|≤R →
      ‖localWord w r-NormedSpace.exp ((t*f r)•axisX)‖<ε := by
  let I := Set.Icc (-R) R
  let : Nonempty I := ⟨⟨0,by constructor <;> linarith⟩⟩
  let s : C(I,ℝ) := ⟨Subtype.val,continuous_subtype_val⟩
  obtain ⟨w,hw⟩ := even_continuous_pulse_approximation s f hf t hε
  refine ⟨w,fun r hr => ?_⟩
  have hi : r∈I := abs_le.mp hr
  have he := (ContinuousMap.norm_lt_iff _ hε).mp hw ⟨r,hi⟩
  simp only [ContinuousMap.sub_apply,field_pulse_apply,field_exp_apply,ContinuousMap.smul_apply] at he
  change ‖localWord w r-NormedSpace.exp (t•(f r•axisX))‖<ε at he
  simpa only [smul_smul] using he

 
theorem odd_localWord_compact (f : C(ℝ,ℝ)) (hf : Function.Odd f) (t R : ℝ)
    (hR : 0≤R) {ε : ℝ} (hε : 0<ε) :
    (∃w : List (Bool×ℝ),∀r : ℝ,|r|≤R →
      ‖localWord w r-NormedSpace.exp ((t*f r)•axisY)‖<ε) ∧
    (∃w : List (Bool×ℝ),∀r : ℝ,|r|≤R →
      ‖localWord w r-NormedSpace.exp ((t*f r)•axisZ)‖<ε) := by
  let I := Set.Icc (-R) R
  let : Nonempty I := ⟨⟨0,by constructor <;> linarith⟩⟩
  let s : C(I,ℝ) := ⟨Subtype.val,continuous_subtype_val⟩
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := odd_continuous_pulse_approximation s f hf t hε
  constructor
  · refine ⟨u,fun r hr => ?_⟩
    have hi : r∈I := abs_le.mp hr
    have he := (ContinuousMap.norm_lt_iff _ hε).mp hu ⟨r,hi⟩
    simp only [ContinuousMap.sub_apply,field_pulse_apply,field_exp_apply,ContinuousMap.smul_apply] at he
    change ‖localWord u r-NormedSpace.exp (t•(f r•axisY))‖<ε at he
    simpa only [smul_smul] using he
  · refine ⟨v,fun r hr => ?_⟩
    have hi : r∈I := abs_le.mp hr
    have he := (ContinuousMap.norm_lt_iff _ hε).mp hv ⟨r,hi⟩
    simp only [ContinuousMap.sub_apply,field_pulse_apply,field_exp_apply,ContinuousMap.smul_apply] at he
    change ‖localWord v r-NormedSpace.exp (t•(f r•axisZ))‖<ε at he
    simpa only [smul_smul] using he

end CompactSeedControl

 

open scoped Topology
open Filter MeasureTheory

namespace CompactSeedControl
local instance yAddQuaternionNormedAlgebraRatTwo : NormedAlgebra ℚ (Quaternion ℝ) := NormedAlgebra.restrictScalars ℚ ℝ (Quaternion ℝ)

 

theorem localWord_sequence {g : ℝ → Quaternion ℝ}
    (hg : ∀R : ℝ,0≤R → ∀ε : ℝ,0<ε → ∃w : List (Bool×ℝ),
      ∀r : ℝ,|r|≤R → ‖localWord w r-g r‖<ε) :
    ∃w : ℕ → List (Bool×ℝ),∀r : ℝ,Tendsto (fun n => localWord (w n) r) atTop (𝓝 (g r)) := by
  have he (n : ℕ) : 0<(1:ℝ)/((n:ℝ)+1) := by positivity
  choose w hw using fun n : ℕ => hg n (Nat.cast_nonneg n) (1/(n+1)) (he n)
  refine ⟨w,fun r => ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
  · have hn : ∀ᶠ n : ℕ in atTop,|r|≤(n:ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
        (eventually_ge_atTop |r|)
    exact hn.mono fun n hn => le_of_lt (hw n r hn)
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

 

theorem localWord_weighted_L2 {g : ℝ → Quaternion ℝ} (hg : Continuous g)
    (hgu : ∀r,g r∈unitary (Quaternion ℝ)) (w : ℕ → List (Bool×ℝ))
    (hw : ∀r,Tendsto (fun n => localWord (w n) r) atTop (𝓝 (g r)))
    (μ : Measure ℝ) (ρ : ℝ → ℝ) (hρ : Integrable ρ μ) :
    Tendsto (fun n => ∫r,|ρ r| *‖localWord (w n) r-g r‖^2 ∂μ) atTop (𝓝 0) := by
  have hd (n : ℕ) (r : ℝ) : ‖localWord (w n) r-g r‖≤2 := by
    calc
      ‖localWord (w n) r-g r‖≤‖localWord (w n) r‖+‖g r‖ := norm_sub_le _ _
      _=2 := by rw [CStarRing.norm_of_mem_unitary (localWord_unitary _ _),
        CStarRing.norm_of_mem_unitary (hgu _)]; norm_num
  have ht := tendsto_integral_of_dominated_convergence
    (F:=fun n r => |ρ r| *‖localWord (w n) r-g r‖^2) (f:=fun _ => (0:ℝ))
    (fun r => 4*|ρ r|)
    (fun n => hρ.abs.aestronglyMeasurable.mul
      (((localWord_continuous (w n)).sub hg).norm.pow 2).aestronglyMeasurable)
    (hρ.abs.const_mul 4) ?_ ?_
  · simpa only [integral_zero] using ht
  · intro n
    exact Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
      have hb := hd n r
      have hn := norm_nonneg (localWord (w n) r-g r)
      have hs : ‖localWord (w n) r-g r‖^2≤4 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg (ρ r))]
  · exact Eventually.of_forall fun r => by
      have hl := (hw r).sub (tendsto_const_nhds (x:=g r))
      have hl' := ((hl.norm).pow 2).const_mul |ρ r|
      simpa using hl'

 

theorem even_localWord_moment (f : C(ℝ,ℝ)) (hf : Function.Even f) (t : ℝ) :
    ∃w : ℕ → List (Bool×ℝ),
      (∀r,Tendsto (fun n => localWord (w n) r) atTop
        (𝓝 (NormedSpace.exp ((t*f r)•axisX)))) ∧
      (∀(μ : Measure ℝ) (ρ : ℝ → ℝ),Integrable ρ μ →
        Tendsto (fun n => ∫r,|ρ r| *‖localWord (w n) r-
          NormedSpace.exp ((t*f r)•axisX)‖^2 ∂μ) atTop (𝓝 0)) := by
  obtain ⟨w,hw⟩ := localWord_sequence (fun R hR ε hε => even_localWord_compact f hf t R hR hε)
  refine ⟨w,hw,fun μ ρ hρ => localWord_weighted_L2 ?_ ?_ w hw μ ρ hρ⟩
  · exact NormedSpace.exp_continuous.comp ((continuous_const.mul f.continuous).smul continuous_const)
  · intro r
    exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem _ axisX_skew)

 

theorem odd_localWord_moment (f : C(ℝ,ℝ)) (hf : Function.Odd f) (t : ℝ) :
    ∀a∈({axisY,axisZ} : Set (Quaternion ℝ)),
    ∃w : ℕ → List (Bool×ℝ),
      (∀r,Tendsto (fun n => localWord (w n) r) atTop
        (𝓝 (NormedSpace.exp ((t*f r)•a)))) ∧
      (∀(μ : Measure ℝ) (ρ : ℝ → ℝ),Integrable ρ μ →
        Tendsto (fun n => ∫r,|ρ r| *‖localWord (w n) r-
          NormedSpace.exp ((t*f r)•a)‖^2 ∂μ) atTop (𝓝 0)) := by
  intro a ha
  have hs : a∈skewAdjoint (Quaternion ℝ) := by
    rcases ha with rfl | ha
    · exact axisY_skew
    · have : a=axisZ := ha
      subst a
      exact axisZ_skew
  have hc : ∀R : ℝ,0≤R → ∀ε : ℝ,0<ε → ∃w : List (Bool×ℝ),
      ∀r : ℝ,|r|≤R → ‖localWord w r-NormedSpace.exp ((t*f r)•a)‖<ε := by
    intro R hR ε hε
    rcases ha with rfl | ha
    · exact (odd_localWord_compact f hf t R hR hε).1
    · have : a=axisZ := ha
      subst a
      exact (odd_localWord_compact f hf t R hR hε).2
  obtain ⟨w,hw⟩ := localWord_sequence hc
  refine ⟨w,hw,fun μ ρ hρ => localWord_weighted_L2 ?_ ?_ w hw μ ρ hρ⟩
  · exact NormedSpace.exp_continuous.comp ((continuous_const.mul f.continuous).smul continuous_const)
  · intro r
    exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem _ hs)

end CompactSeedControl

 

open scoped Topology ENNReal
open Filter MeasureTheory

namespace CompactSeedControl

 

theorem continuous_sequence_ae (μ : Measure ℝ) [μ.WeaklyRegular]
    {f : ℝ → ℝ} (hf : MemLp f 1 μ) :
    ∃g : ℕ → C(ℝ,ℝ),∀ᵐ r ∂μ,Tendsto (fun n => g n r) atTop (𝓝 (f r)) := by
  have he (n : ℕ) : ENNReal.ofReal ((1:ℝ)/(n+1))≠0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  choose g hg hm using fun n : ℕ => hf.exists_boundedContinuous_eLpNorm_sub_le
    ENNReal.one_ne_top (he n)
  have ht : Tendsto (fun n => eLpNorm ((g n : ℝ → ℝ)-f) 1 μ) atTop (𝓝 0) := by
    have ht0 : Tendsto (fun n : ℕ => ENNReal.ofReal ((1:ℝ)/(n+1))) atTop (𝓝 0) := by
      simpa only [Function.comp_def,ENNReal.ofReal_zero] using
        (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht0
      (fun _ => bot_le)
    intro n
    simpa only [eLpNorm_sub_comm] using hg n
  obtain ⟨u,hu,hu'⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (1:ℝ≥0∞)≠0) ht).exists_seq_tendsto_ae
  exact ⟨fun n => (g (u n)).toContinuousMap,hu'⟩

 

theorem even_continuous_sequence_ae (μ : Measure ℝ) [μ.WeaklyRegular]
    (hμ : MeasurePreserving (fun r : ℝ => -r) μ μ)
    {f : ℝ → ℝ} (hf : MemLp f 1 μ) (he : Function.Even f) :
    ∃g : ℕ → C(ℝ,ℝ),(∀n,Function.Even (g n)) ∧
      ∀ᵐ r ∂μ,Tendsto (fun n => g n r) atTop (𝓝 (f r)) := by
  obtain ⟨g,hg⟩ := continuous_sequence_ae μ hf
  let b (n : ℕ) : C(ℝ,ℝ) := ⟨fun r => (g n r+g n (-r))/2,by fun_prop⟩
  refine ⟨b,fun n r => ?_,?_⟩
  · change (g n (-r)+g n (-(-r)))/2=(g n r+g n (-r))/2
    simp only [neg_neg]
    ring
  · have hgn := hμ.quasiMeasurePreserving.ae hg
    filter_upwards [hg,hgn] with r hr hnr
    have ht := (hr.add hnr).div_const 2
    rw [he r,add_self_div_two] at ht
    exact ht

theorem odd_continuous_sequence_ae (μ : Measure ℝ) [μ.WeaklyRegular]
    (hμ : MeasurePreserving (fun r : ℝ => -r) μ μ)
    {f : ℝ → ℝ} (hf : MemLp f 1 μ) (he : Function.Odd f) :
    ∃g : ℕ → C(ℝ,ℝ),(∀n,Function.Odd (g n)) ∧
      ∀ᵐ r ∂μ,Tendsto (fun n => g n r) atTop (𝓝 (f r)) := by
  obtain ⟨g,hg⟩ := continuous_sequence_ae μ hf
  let b (n : ℕ) : C(ℝ,ℝ) := ⟨fun r => (g n r-g n (-r))/2,by fun_prop⟩
  refine ⟨b,fun n r => ?_,?_⟩
  · change (g n (-r)-g n (-(-r)))/2= -((g n r-g n (-r))/2)
    simp only [neg_neg]
    ring
  · have hgn := hμ.quasiMeasurePreserving.ae hg
    filter_upwards [hg,hgn] with r hr hnr
    have ht := (hr.sub hnr).div_const 2
    rw [he r,sub_neg_eq_add,add_self_div_two] at ht
    exact ht

end CompactSeedControl

 

open scoped Topology
open Filter MeasureTheory

namespace CompactSeedControl
local instance yAddQuaternionNormedAlgebraRatThree : NormedAlgebra ℚ (Quaternion ℝ) := NormedAlgebra.restrictScalars ℚ ℝ (Quaternion ℝ)

 

theorem localWord_diagonal {g : ℕ → ℝ → Quaternion ℝ}
    (hg : ∀n : ℕ,∀R : ℝ,0≤R → ∀ε : ℝ,0<ε → ∃w : List (Bool×ℝ),
      ∀r : ℝ,|r|≤R → ‖localWord w r-g n r‖<ε) :
    ∃w : ℕ → List (Bool×ℝ),∀r : ℝ,
      Tendsto (fun n => localWord (w n) r-g n r) atTop (𝓝 0) := by
  have he (n : ℕ) : 0<(1:ℝ)/((n:ℝ)+1) := by positivity
  choose w hw using fun n : ℕ => hg n n (Nat.cast_nonneg n) (1/(n+1)) (he n)
  refine ⟨w,fun r => ?_⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
  · have hn : ∀ᶠ n : ℕ in atTop,|r|≤(n:ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
        (eventually_ge_atTop |r|)
    exact hn.mono fun n hn => le_of_lt (hw n r hn)
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

 

theorem localWord_weighted_L2_ae {g : ℝ → Quaternion ℝ} (μ : Measure ℝ)
    (hg : AEStronglyMeasurable g μ) (hgu : ∀r,g r∈unitary (Quaternion ℝ))
    (w : ℕ → List (Bool×ℝ))
    (hw : ∀ᵐ r ∂μ,Tendsto (fun n => localWord (w n) r) atTop (𝓝 (g r)))
    (ρ : ℝ → ℝ) (hρ : Integrable ρ μ) :
    Tendsto (fun n => ∫r,|ρ r| *‖localWord (w n) r-g r‖^2 ∂μ) atTop (𝓝 0) := by
  have hd (n : ℕ) (r : ℝ) : ‖localWord (w n) r-g r‖≤2 := by
    calc
      ‖localWord (w n) r-g r‖≤‖localWord (w n) r‖+‖g r‖ := norm_sub_le _ _
      _=2 := by rw [CStarRing.norm_of_mem_unitary (localWord_unitary _ _),
        CStarRing.norm_of_mem_unitary (hgu _)]; norm_num
  have ht := tendsto_integral_of_dominated_convergence
    (F:=fun n r => |ρ r| *‖localWord (w n) r-g r‖^2) (f:=fun _ => (0:ℝ))
    (fun r => 4*|ρ r|)
    (fun n => hρ.abs.aestronglyMeasurable.mul
      ((((localWord_continuous (w n)).aestronglyMeasurable.sub hg).norm).pow 2))
    (hρ.abs.const_mul 4) ?_ ?_
  · simpa only [integral_zero] using ht
  · intro n
    exact Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
      have hb := hd n r
      have hn := norm_nonneg (localWord (w n) r-g r)
      have hs : ‖localWord (w n) r-g r‖^2≤4 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg (ρ r))]
  · filter_upwards [hw] with r hr
    have hl := hr.sub (tendsto_const_nhds (x:=g r))
    have hl' := ((hl.norm).pow 2).const_mul |ρ r|
    simpa using hl'

 

theorem even_measurable_localWord (μ : Measure ℝ) [μ.WeaklyRegular]
    (hμ : MeasurePreserving (fun r : ℝ => -r) μ μ)
    {f : ℝ → ℝ} (hf : MemLp f 1 μ) (he : Function.Even f) (t : ℝ) :
    ∃w : ℕ → List (Bool×ℝ),
      (∀ᵐ r ∂μ,Tendsto (fun n => localWord (w n) r) atTop
        (𝓝 (NormedSpace.exp ((t*f r)•axisX)))) ∧
      (∀ρ : ℝ → ℝ,Integrable ρ μ →
        Tendsto (fun n => ∫r,|ρ r| *‖localWord (w n) r-
          NormedSpace.exp ((t*f r)•axisX)‖^2 ∂μ) atTop (𝓝 0)) := by
  obtain ⟨g,hge,hg⟩ := even_continuous_sequence_ae μ hμ hf he
  obtain ⟨w,hw⟩ := localWord_diagonal (fun n R hR ε hε =>
    even_localWord_compact (g n) (hge n) t R hR hε)
  have ha : ∀ᵐ r ∂μ,Tendsto (fun n => localWord (w n) r) atTop
      (𝓝 (NormedSpace.exp ((t*f r)•axisX))) := by
    filter_upwards [hg] with r hr
    have ht := NormedSpace.exp_continuous.continuousAt.tendsto.comp
      ((hr.const_mul t).smul_const axisX)
    simpa only [Function.comp_def,sub_add_cancel,zero_add] using (hw r).add ht
  refine ⟨w,ha,fun ρ hρ => localWord_weighted_L2_ae μ ?_ ?_ w ha ρ hρ⟩
  · exact NormedSpace.exp_continuous.comp_aestronglyMeasurable
      ((hf.aestronglyMeasurable.const_mul t).smul_const axisX)
  · intro r
    exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem _ axisX_skew)

 

theorem odd_measurable_localWord (μ : Measure ℝ) [μ.WeaklyRegular]
    (hμ : MeasurePreserving (fun r : ℝ => -r) μ μ)
    {f : ℝ → ℝ} (hf : MemLp f 1 μ) (he : Function.Odd f) (t : ℝ) :
    ∀a∈({axisY,axisZ} : Set (Quaternion ℝ)),
    ∃w : ℕ → List (Bool×ℝ),
      (∀ᵐ r ∂μ,Tendsto (fun n => localWord (w n) r) atTop
        (𝓝 (NormedSpace.exp ((t*f r)•a)))) ∧
      (∀ρ : ℝ → ℝ,Integrable ρ μ →
        Tendsto (fun n => ∫r,|ρ r| *‖localWord (w n) r-
          NormedSpace.exp ((t*f r)•a)‖^2 ∂μ) atTop (𝓝 0)) := by
  intro a ha
  have hs : a∈skewAdjoint (Quaternion ℝ) := by
    rcases ha with rfl | ha
    · exact axisY_skew
    · have : a=axisZ := ha
      subst a
      exact axisZ_skew
  obtain ⟨g,hge,hg⟩ := odd_continuous_sequence_ae μ hμ hf he
  have hgc : ∀n : ℕ,∀R : ℝ,0≤R → ∀ε : ℝ,0<ε → ∃w : List (Bool×ℝ),
      ∀r : ℝ,|r|≤R → ‖localWord w r-NormedSpace.exp ((t*g n r)•a)‖<ε := by
    intro n R hR ε hε
    rcases ha with rfl | ha
    · exact (odd_localWord_compact (g n) (hge n) t R hR hε).1
    · have : a=axisZ := ha
      subst a
      exact (odd_localWord_compact (g n) (hge n) t R hR hε).2
  obtain ⟨w,hw⟩ := localWord_diagonal hgc
  have ha : ∀ᵐ r ∂μ,Tendsto (fun n => localWord (w n) r) atTop
      (𝓝 (NormedSpace.exp ((t*f r)•a))) := by
    filter_upwards [hg] with r hr
    have ht := NormedSpace.exp_continuous.continuousAt.tendsto.comp
      ((hr.const_mul t).smul_const a)
    simpa only [Function.comp_def,sub_add_cancel,zero_add] using (hw r).add ht
  refine ⟨w,ha,fun ρ hρ => localWord_weighted_L2_ae μ ?_ ?_ w ha ρ hρ⟩
  · exact NormedSpace.exp_continuous.comp_aestronglyMeasurable
      ((hf.aestronglyMeasurable.const_mul t).smul_const a)
  · intro r
    exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem _ hs)

end CompactSeedControl

 

open scoped BigOperators Matrix Topology Matrix.Norms.Operator

namespace MaskSign
variable {C : Type*} [Fintype C] [DecidableEq C]

def sign (ε : C → Bool) (a : C) : ℂ := if ε a then -1 else 1

omit [Fintype C] [DecidableEq C] in
@[simp] theorem sign_sq (ε : C → Bool) (a : C) : sign ε a*sign ε a=1 := by
  cases h : ε a <;> simp [sign,h]

def flipEquiv (a : C) : (C → Bool) ≃ (C → Bool) where
  toFun ε := Function.update ε a (!(ε a))
  invFun ε := Function.update ε a (!(ε a))
  left_inv ε := by funext b; by_cases h : b=a <;> simp [h,Function.update]
  right_inv ε := by funext b; by_cases h : b=a <;> simp [h,Function.update]

omit [Fintype C] in
@[simp] theorem sign_flip_same (ε : C → Bool) (a : C) :
    sign (flipEquiv a ε) a= -sign ε a := by
  cases h : ε a <;> simp [sign,flipEquiv,h]

omit [Fintype C] in
@[simp] theorem sign_flip_ne (ε : C → Bool) (a b : C) (h : b≠a) :
    sign (flipEquiv a ε) b=sign ε b := by
  simp [sign,flipEquiv,Function.update_of_ne h]

 
theorem sum_character (S : Finset C) :
    (∑ε : C → Bool,∏a∈S,sign ε a)=if S=∅ then (2:ℂ)^(Fintype.card C) else 0 := by
  by_cases hs : S=∅
  · subst S
    simp
  · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hf (ε : C → Bool) :
        (∏b∈S,sign (flipEquiv a ε) b)= -(∏b∈S,sign ε b) := by
      rw [←Finset.mul_prod_erase S _ ha,←Finset.mul_prod_erase S _ ha,sign_flip_same]
      have he : (∏b∈S.erase a,sign (flipEquiv a ε) b)=∏b∈S.erase a,sign ε b := by
        apply Finset.prod_congr rfl
        intro b hb
        exact sign_flip_ne _ _ _ (Finset.ne_of_mem_erase hb)
      rw [he,neg_mul]
    have he := Equiv.sum_comp (flipEquiv a) (fun ε => ∏b∈S,sign ε b)
    simp_rw [hf,Finset.sum_neg_distrib] at he
    rw [ite_eq_right hs]
    have : (2:ℂ)*(∑ε : C → Bool,∏b∈S,sign ε b)=0 := by linear_combination -he
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)

 
theorem sum_two {a b : C} (h : a≠b) : (∑ε : C → Bool,sign ε a*sign ε b)=0 := by
  simpa [Finset.prod_pair h] using sum_character ({a,b} : Finset C)

theorem sum_flip_zero (a : C) (f : (C → Bool) → ℂ)
    (hf : ∀ε,f (flipEquiv a ε)= -f ε) : (∑ε,f ε)=0 := by
  have he := Equiv.sum_comp (flipEquiv a) f
  simp_rw [hf,Finset.sum_neg_distrib] at he
  have : (2:ℂ)*(∑ε,f ε)=0 := by linear_combination -he
  exact (mul_eq_zero.mp this).resolve_left (by norm_num)

 

theorem sum_four {a b : C} (hab : a≠b) (c d : C) :
    (∑ε : C → Bool,sign ε a*sign ε b*sign ε c*sign ε d)=
      if (a=c ∧ b=d) ∨ (a=d ∧ b=c) then (2:ℂ)^(Fintype.card C) else 0 := by
  by_cases hac : a=c
  · subst c
    have he (ε : C → Bool) : sign ε a*sign ε b*sign ε a*sign ε d=sign ε b*sign ε d := by
      calc
        _=(sign ε a*sign ε a)*(sign ε b*sign ε d) := by ring
        _=_ := by rw [sign_sq,one_mul]
    simp_rw [he]
    by_cases hbd : b=d
    · subst d
      simp [sign_sq,hab]
    · rw [sum_two hbd]
      simp [hbd,Ne.symm hab]
  · by_cases had : a=d
    · subst d
      have he (ε : C → Bool) : sign ε a*sign ε b*sign ε c*sign ε a=sign ε b*sign ε c := by
        calc
          _=(sign ε a*sign ε a)*(sign ε b*sign ε c) := by ring
          _=_ := by rw [sign_sq,one_mul]
      simp_rw [he]
      by_cases hbc : b=c
      · subst c
        simp [sign_sq,hab]
      · rw [sum_two hbc]
        simp [hac,hbc]
    · rw [ite_eq_right (by simp [hac,had])]
      apply sum_flip_zero a
      intro ε
      rw [sign_flip_same,sign_flip_ne ε a b (Ne.symm hab),
        sign_flip_ne ε a c (Ne.symm hac),sign_flip_ne ε a d (Ne.symm had)]
      ring

end MaskSign

end

end OAI
