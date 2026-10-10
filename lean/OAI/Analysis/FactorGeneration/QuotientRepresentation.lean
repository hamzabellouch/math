import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.ContinuousMap.Bounded.Star
import OAI.Analysis.FactorGeneration.OperatorLimits
import OAI.Analysis.FactorGeneration.QuotientHilbert

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete operator-norm bounded sequences and their contractive map to the
actual quotient trace Hilbert space. This map is not asserted injective. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

abbrev Sequences (M : VonNeumannAlgebra H) := BoundedContinuousFunction ℕ M.toStarSubalgebra

instance sequencesIsTopologicalRing : IsTopologicalRing (Sequences M) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing (Sequences M) inferInstance

/-- Forget continuity (automatic on the discrete index set) and retain boundedness. -/
def boundedMap : Sequences M →⋆ₐ[ℂ] Bounded M where
  toFun a := ⟨a, ⟨‖a‖, norm_nonneg a, a.norm_coe_le_norm⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem boundedMap_surjective : Function.Surjective (boundedMap (M := M)) := by
  intro a
  obtain ⟨C, _, hC⟩ := a.property
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete a.val C hC, ?_⟩
  apply Subtype.ext
  funext n
  rfl

/-- The actual star-algebra quotient map on complete bounded sequences. -/
def sequenceQuotient : Sequences M →⋆ₐ[ℂ] Q τ ω :=
  (quotientStarAlgHom τ (ω : Filter ℕ)).comp boundedMap

theorem sequenceQuotient_surjective : Function.Surjective (sequenceQuotient τ ω) := by
  intro q
  obtain ⟨b, rfl⟩ := quotientMap_surjective τ (ω : Filter ℕ) q
  obtain ⟨a, rfl⟩ := boundedMap_surjective b
  exact ⟨a, rfl⟩

theorem quotient_norm_tendsto (a : Bounded M) :
    Tendsto (fun n => τ.norm₂ (a.val n)) (ω : Filter ℕ)
      (𝓝 ‖quotientMap τ (ω : Filter ℕ) a‖) := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_eq_trace]
  exact norm₂_tendsto τ ω a

theorem sequence_norm_tendsto (a : Sequences M) :
    Tendsto (fun n => τ.norm₂ (a n)) (ω : Filter ℕ) (𝓝 ‖sequenceQuotient τ ω a‖) := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_eq_trace]
  exact norm₂_tendsto τ ω (boundedMap a)

theorem sequenceQuotient_norm_le (a : Sequences M) :
    ‖sequenceQuotient τ ω a‖ ≤ ‖a‖ := by
  apply le_of_tendsto (sequence_norm_tendsto τ ω a)
  exact Eventually.of_forall (fun n => (τ.norm₂_le_norm (a n)).trans (a.norm_coe_le_norm n))

/-- The continuous Hilbert realization used by the analytic remainder theorem. -/
def sequenceInclusion : Sequences M →L[ℂ] L2 τ ω :=
  LinearMap.mkContinuous
    { toFun := fun a => inclusion τ ω (sequenceQuotient τ ω a)
      map_add' := by intros; simp only [map_add]
      map_smul' := by intros; simp only [map_smul]; rfl } 1
    (by
      intro a
      change ‖inclusion τ ω (sequenceQuotient τ ω a)‖ ≤ 1*‖a‖
      rw [LinearIsometry.norm_map, one_mul]
      exact sequenceQuotient_norm_le τ ω a)

@[simp] theorem sequenceInclusion_apply (a : Sequences M) :
    sequenceInclusion τ ω a = inclusion τ ω (sequenceQuotient τ ω a) := rfl

theorem sequenceInclusion_norm_le (a : Sequences M) : ‖sequenceInclusion τ ω a‖ ≤ ‖a‖ := by
  rw [sequenceInclusion_apply, LinearIsometry.norm_map]
  exact sequenceQuotient_norm_le τ ω a

/-- Literal ultralimit inner product, including the complex orientation. -/
theorem sequence_inner_tendsto (a b : Sequences M) :
    Tendsto (fun n => τ.trace (star (a n)*b n)) (ω : Filter ℕ)
      (𝓝 (inner ℂ (sequenceInclusion τ ω a) (sequenceInclusion τ ω b))) := by
  rw [sequenceInclusion_apply, sequenceInclusion_apply, inclusion_inner]
  exact traceRep_tendsto τ ω (star (boundedMap a)*boundedMap b)

/-- The kernel consists exactly of trace-null bounded sequences. -/
theorem sequenceInclusion_eq_zero_iff (a : Sequences M) :
    sequenceInclusion τ ω a = 0 ↔ Tendsto (fun n => τ.norm₂ (a n)) (ω : Filter ℕ) (𝓝 0) := by
  rw [sequenceInclusion_apply, ← (inclusion τ ω).map_zero,
    (inclusion τ ω).injective.eq_iff]
  change quotientMap τ (ω : Filter ℕ) (boundedMap a) = quotientMap τ (ω : Filter ℕ) 0 ↔ _
  rw [quotientMap_eq_iff]
  change Tendsto (fun n => τ.norm₂ (a n - 0)) (ω : Filter ℕ) (𝓝 0) ↔ _
  simp only [sub_zero]

end

/-! The faithful constant embedding into the tracial quotient, with its trace and trace norm, for every ultrafilter. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def constantSequence : M.toStarSubalgebra →⋆ₐ[ℂ] Sequences M where
  toFun := BoundedContinuousFunction.const ℕ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def constantQuotient : M.toStarSubalgebra →⋆ₐ[ℂ] Q τ ω :=
  (sequenceQuotient τ ω).comp constantSequence

@[simp] theorem constantQuotient_trace (a : M.toStarSubalgebra) :
    quotientTrace τ ω (constantQuotient τ ω a) = τ.trace a := by
  exact tendsto_nhds_unique (traceRep_tendsto τ ω (boundedMap (constantSequence a)))
    tendsto_const_nhds

@[simp] theorem constantQuotient_norm (a : M.toStarSubalgebra) :
    ‖constantQuotient τ ω a‖ = τ.norm₂ a := by
  exact tendsto_nhds_unique (sequence_norm_tendsto τ ω (constantSequence a)) tendsto_const_nhds

/-- No nonzero constant element is killed by the tracial quotient ideal. -/
theorem constantQuotient_injective : Function.Injective (constantQuotient τ ω) := by
  intro a b h
  apply sub_eq_zero.mp
  apply (τ.norm₂_eq_zero_iff (a-b)).mp
  rw [← constantQuotient_norm τ ω, map_sub, h, sub_self, norm_zero]

@[simp] theorem constantQuotient_inner (a b : M.toStarSubalgebra) :
    inner ℂ (inclusion τ ω (constantQuotient τ ω a))
      (inclusion τ ω (constantQuotient τ ω b)) = τ.trace (star a*b) := by
  rw [inclusion_inner, ← map_star, ← map_mul, constantQuotient_trace]

end

/-! Left multiplication by bounded representatives on the completed trace
Hilbert space. The quotient ideal, not an assumed operator action, determines
which representatives induce the same operator. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem sequence_mul_norm_le (a : Sequences M) (b : Q τ ω) :
    ‖sequenceQuotient τ ω a*b‖ ≤ ‖a‖*‖b‖ := by
  induction b using Quotient.inductionOn with
  | h b =>
    have hp := quotient_norm_tendsto τ ω (boundedMap a*b)
    have hb := (quotient_norm_tendsto τ ω b).const_mul ‖a‖
    apply le_of_tendsto_of_tendsto hp hb
    exact Eventually.of_forall (fun n =>
      (τ.norm₂_mul_le (a n) (b.val n)).trans
        (mul_le_mul_of_nonneg_right (a.norm_coe_le_norm n) (norm_nonneg _)))

def leftOnQuotient (a : Sequences M) : Q τ ω →L[ℂ] Q τ ω :=
  LinearMap.mkContinuous (LinearMap.mulLeft ℂ (sequenceQuotient τ ω a)) ‖a‖
    (sequence_mul_norm_le τ ω a)

@[simp] theorem leftOnQuotient_apply (a : Sequences M) (b : Q τ ω) :
    leftOnQuotient τ ω a b = sequenceQuotient τ ω a*b := rfl

theorem inclusion_denseRange : DenseRange (inclusion τ ω) :=
  UniformSpace.Completion.denseRange_coe

/-- Bounded left multiplication extended to the actual Hilbert completion. -/
def leftAction (a : Sequences M) : L2 τ ω →L[ℂ] L2 τ ω :=
  ((inclusion τ ω).toContinuousLinearMap.comp (leftOnQuotient τ ω a)).extend
    (inclusion τ ω).toContinuousLinearMap

@[simp] theorem leftAction_inclusion (a : Sequences M) (b : Q τ ω) :
    leftAction τ ω a (inclusion τ ω b) = inclusion τ ω (sequenceQuotient τ ω a*b) := by
  exact ContinuousLinearMap.extend_eq
    ((inclusion τ ω).toContinuousLinearMap.comp (leftOnQuotient τ ω a))
    (e := (inclusion τ ω).toContinuousLinearMap)
    (inclusion_denseRange τ ω) ((inclusion τ ω).isometry.isUniformInducing) b

@[simp] theorem leftAction_coe (a : Sequences M) (b : Q τ ω) :
    leftAction τ ω a (b : L2 τ ω) = ((sequenceQuotient τ ω a*b : Q τ ω) : L2 τ ω) :=
  leftAction_inclusion τ ω a b

theorem leftAction_norm_le (a : Sequences M) : ‖leftAction τ ω a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  apply isClosed_property (inclusion_denseRange τ ω)
    (isClosed_le (by fun_prop) (by fun_prop))
  intro b
  simpa only [leftAction_inclusion, LinearIsometry.norm_map] using sequence_mul_norm_le τ ω a b

@[simp] theorem leftAction_one : leftAction τ ω 1 = 1 := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [leftAction_coe, map_one, one_mul, one_apply_eq_self]

@[simp] theorem leftAction_mul (a b : Sequences M) :
    leftAction τ ω (a*b) = leftAction τ ω a*leftAction τ ω b := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [mul_apply_eq_comp, leftAction_coe, map_mul, mul_assoc]

@[simp] theorem leftAction_add (a b : Sequences M) :
    leftAction τ ω (a+b) = leftAction τ ω a+leftAction τ ω b := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [add_apply, leftAction_coe, map_add, add_mul, UniformSpace.Completion.coe_add]

private theorem completionT2Space (E : Type*) [UniformSpace E] :
    T2Space (UniformSpace.Completion E) := inferInstance

@[simp] theorem leftAction_smul (c : ℂ) (a : Sequences M) :
    leftAction τ ω (c • a) = c • leftAction τ ω a := by
  let : T2Space (L2 τ ω) := completionT2Space (Q τ ω)
  apply ContinuousLinearMap.coeFn_injective
  apply (inclusion_denseRange τ ω).equalizer (leftAction τ ω (c • a)).continuous
    ((c • leftAction τ ω a : L2 τ ω →L[ℂ] L2 τ ω)).continuous
  funext b
  change leftAction τ ω (c • a) (inclusion τ ω b) = c • leftAction τ ω a (inclusion τ ω b)
  calc
    _ = inclusion τ ω (sequenceQuotient τ ω (c • a)*b) := leftAction_inclusion τ ω (c • a) b
    _ = inclusion τ ω (c • (sequenceQuotient τ ω a*b)) :=
      congrArg (inclusion τ ω)
        ((congrArg (fun z : Q τ ω => z*b) (map_smul (sequenceQuotient τ ω) c a)).trans
          (smul_mul_assoc c (sequenceQuotient τ ω a) b))
    _ = c • inclusion τ ω (sequenceQuotient τ ω a*b) := (inclusion τ ω).map_smul c _
    _ = _ := congrArg (fun z : L2 τ ω => c • z) (leftAction_inclusion τ ω a b).symm

@[simp] theorem leftAction_zero : leftAction τ ω 0 = 0 := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [leftAction_coe, map_zero, zero_mul, zero_apply, UniformSpace.Completion.coe_zero]

@[simp] theorem leftAction_star (a : Sequences M) :
    leftAction τ ω (star a) = star (leftAction τ ω a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b c
  simp only [leftAction_coe, UniformSpace.Completion.inner_coe, inner_eq_trace, map_star, star_mul, star_star, mul_assoc]

/-- A concrete star-algebra action, constructed from the trace quotient. -/
def sequenceAction : Sequences M →⋆ₐ[ℂ] (L2 τ ω →L[ℂ] L2 τ ω) where
  toFun := leftAction τ ω
  map_one' := leftAction_one τ ω
  map_mul' := leftAction_mul τ ω
  map_zero' := leftAction_zero τ ω
  map_add' := leftAction_add τ ω
  commutes' c := by
    change leftAction τ ω (algebraMap ℂ (Sequences M) c) = algebraMap ℂ (L2 τ ω →L[ℂ] L2 τ ω) c
    calc
      _ = leftAction τ ω (c • (1 : Sequences M)) := congrArg (leftAction τ ω) (Algebra.algebraMap_eq_smul_one c)
      _ = c • (1 : L2 τ ω →L[ℂ] L2 τ ω) :=
        (leftAction_smul τ ω c 1).trans
          (congrArg (fun T : L2 τ ω →L[ℂ] L2 τ ω => c • T) (leftAction_one τ ω))
      _ = _ := (Algebra.algebraMap_eq_smul_one c).symm
  map_star' := leftAction_star τ ω

/-- Equality of operators is precisely equality in the tracial quotient. -/
theorem leftAction_eq_iff (a b : Sequences M) :
    leftAction τ ω a = leftAction τ ω b ↔ sequenceQuotient τ ω a = sequenceQuotient τ ω b := by
  constructor
  · intro h
    have he := congrArg (fun T : L2 τ ω →L[ℂ] L2 τ ω => T (inclusion τ ω 1)) h
    simpa only [leftAction_inclusion, mul_one, (inclusion τ ω).injective.eq_iff] using he
  · intro h
    ext x
    refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro c
    simp only [leftAction_coe, h]

end

/-! Faithful concrete Hilbert-space representation of the tracial quotient
star algebra. Weak operator closedness of its image is not claimed here. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
section Descent
variable {A B C : Type*} [Ring A] [Ring B] [Ring C]
  [StarRing A] [StarRing B] [StarRing C]
  [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]

/-- Descend a proved compatible map through a surjective star-algebra map. -/
def descendStarAlgHom (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (f : A →⋆ₐ[ℂ] C) (g : B → C) (hg : ∀ a, g (q a) = f a) : B →⋆ₐ[ℂ] C where
  toFun := g
  map_one' := by rw [← (map_one q), hg, (map_one f)]
  map_mul' x y := by
    obtain ⟨a,rfl⟩ := hq x
    obtain ⟨b,rfl⟩ := hq y
    rw [← (map_mul q), hg, (map_mul f), hg, hg]
  map_zero' := by rw [← (map_zero q), hg, (map_zero f)]
  map_add' x y := by
    obtain ⟨a,rfl⟩ := hq x
    obtain ⟨b,rfl⟩ := hq y
    rw [← (map_add q), hg, (map_add f), hg, hg]
  commutes' c := by
    have hq : q (algebraMap ℂ A c) = algebraMap ℂ B c := q.commutes c
    have hf : f (algebraMap ℂ A c) = algebraMap ℂ C c := f.commutes c
    rw [← hq, hg, hf]
  map_star' x := by
    obtain ⟨a,rfl⟩ := hq x
    rw [← map_star q, hg, map_star f, hg]
end Descent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def quotientOperator (a : Q τ ω) : L2 τ ω →L[ℂ] L2 τ ω :=
  leftAction τ ω ((sequenceQuotient_surjective τ ω a).choose)

@[simp] theorem quotientOperator_mk (a : Sequences M) :
    quotientOperator τ ω (sequenceQuotient τ ω a) = leftAction τ ω a := by
  apply (leftAction_eq_iff τ ω _ a).mpr
  exact (sequenceQuotient_surjective τ ω (sequenceQuotient τ ω a)).choose_spec

@[simp] theorem sequenceAction_apply (a : Sequences M) :
    sequenceAction τ ω a = leftAction τ ω a := rfl

/-- The quotient itself, rather than a chosen representative algebra, acts
faithfully by bounded Hilbert-space operators. -/
def quotientRepresentation : Q τ ω →⋆ₐ[ℂ] (L2 τ ω →L[ℂ] L2 τ ω) :=
  descendStarAlgHom (A := Sequences M) (B := Q τ ω) (C := L2 τ ω →L[ℂ] L2 τ ω)
    (sequenceQuotient τ ω) (sequenceQuotient_surjective τ ω)
    (sequenceAction τ ω) (quotientOperator τ ω) (fun a =>
      (quotientOperator_mk τ ω a).trans (sequenceAction_apply τ ω a).symm)

@[simp] theorem quotientRepresentation_inclusion (a b : Q τ ω) :
    quotientRepresentation τ ω a (inclusion τ ω b) = inclusion τ ω (a*b) := by
  change quotientOperator τ ω a (inclusion τ ω b) = _
  obtain ⟨s,hs⟩ := sequenceQuotient_surjective τ ω a
  have ho : quotientOperator τ ω a=leftAction τ ω s :=
    (congrArg (quotientOperator τ ω) hs.symm).trans (quotientOperator_mk τ ω s)
  exact (congrArg (fun T : L2 τ ω →L[ℂ] L2 τ ω => T (inclusion τ ω b)) ho).trans
    ((leftAction_inclusion τ ω s b).trans (congrArg (fun z : Q τ ω => inclusion τ ω (z*b)) hs))

/-- The identity vector separates all represented quotient elements. -/
theorem quotientRepresentation_separating (a : Q τ ω)
    (h : quotientRepresentation τ ω a (inclusion τ ω 1) = 0) : a = 0 := by
  apply (inclusion τ ω).injective
  rw [(inclusion τ ω).map_zero]
  simpa only [quotientRepresentation_inclusion, mul_one] using h

theorem quotientRepresentation_injective : Function.Injective (quotientRepresentation τ ω) := by
  intro a b h
  have he := congrArg (fun T : L2 τ ω →L[ℂ] L2 τ ω => T (inclusion τ ω 1)) h
  simpa only [quotientRepresentation_inclusion, mul_one,
    (inclusion τ ω).injective.eq_iff] using he

/-- The represented vector trace is precisely the original ultralimit trace. -/
theorem quotientRepresentation_trace (a : Q τ ω) :
    inner ℂ (inclusion τ ω 1) (quotientRepresentation τ ω a (inclusion τ ω 1)) =
      quotientTrace τ ω a := by
  simp only [quotientRepresentation_inclusion, mul_one, inclusion_inner, star_one, one_mul]

end

/-! The standard completion/continuous-linear-map structures are not new hypotheses. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[instance_reducible] def quotientL2AddCommMonoid : AddCommMonoid (L2 τ ω) :=
  (inferInstance : NormedAddCommGroup (L2 τ ω)).toAddCommGroup.toAddCommMonoid

@[instance_reducible] def quotientL2AddCommGroup : AddCommGroup (L2 τ ω) :=
  (inferInstance : NormedAddCommGroup (L2 τ ω)).toAddCommGroup

attribute [local instance] quotientL2AddCommMonoid quotientL2AddCommGroup

@[instance_reducible] def quotientOperatorSemiring : Semiring (L2 τ ω →L[ℂ] L2 τ ω) :=
  (inferInstance : NormedRing (L2 τ ω →L[ℂ] L2 τ ω)).toRing.toSemiring

@[instance_reducible] def quotientOperatorNonAssocSemiring : NonUnitalNonAssocSemiring (L2 τ ω →L[ℂ] L2 τ ω) :=
  (inferInstance : NormedRing (L2 τ ω →L[ℂ] L2 τ ω)).toRing.toSemiring.toNonUnitalSemiring.toNonUnitalNonAssocSemiring

attribute [local instance] quotientOperatorSemiring quotientOperatorNonAssocSemiring

@[instance_reducible] def quotientOperatorAlgebra : Algebra ℂ (L2 τ ω →L[ℂ] L2 τ ω) :=
  ContinuousLinearMap.algebra

attribute [local instance] quotientOperatorAlgebra

theorem quotientOperatorSemitopology : IsSemitopologicalSemiring (L2 τ ω →L[ℂ] L2 τ ω) :=
  inferInstance

end

/-! Fixed-index selection for bounded coordinate representatives. -/
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def sequenceEval (n : ℕ) : Sequences M →ₐ[ℂ] M.toStarSubalgebra where
  toFun a := a n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Operator-norm exponentials of bounded sequences evaluate coordinatewise. -/
theorem sequence_exp_apply (a : Sequences M) (n : ℕ) :
    (NormedSpace.exp a) n = NormedSpace.exp (a n) :=
  NormedSpace.map_exp (sequenceEval n)
    (BoundedContinuousFunction.lipschitz_eval_const n).continuous a

theorem sequence_exp_product_apply (a : List (Sequences M)) (n : ℕ) :
    ((a.map NormedSpace.exp).prod) n =
      (a.map (fun b => NormedSpace.exp (b n))).prod := by
  induction a with
  | nil => rfl
  | cons b a ih =>
    change (NormedSpace.exp b) n * ((a.map NormedSpace.exp).prod) n =
      NormedSpace.exp (b n) * (a.map (fun b => NormedSpace.exp (b n))).prod
    rw [sequence_exp_apply, ih]

/-- Both limits hold at one coordinate, with the same positive tolerance. -/
theorem select_coordinate (a ξ b : Sequences M) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, τ.norm₂ (a n) < ‖sequenceQuotient τ ω a‖ + ε ∧
      ‖τ.trace (star (ξ n)*b n) -
        inner ℂ (sequenceInclusion τ ω ξ) (sequenceInclusion τ ω b)‖ < ε := by
  have hn : ∀ᶠ n in (ω : Filter ℕ), τ.norm₂ (a n) < ‖sequenceQuotient τ ω a‖ + ε :=
    (sequence_norm_tendsto τ ω a)
    (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  have ht := Metric.tendsto_nhds.mp (sequence_inner_tendsto τ ω ξ b) ε hε
  obtain ⟨n, hn, ht⟩ := (hn.and ht).exists
  exact ⟨n, hn, by simpa only [dist_eq_norm] using ht⟩

/-- Source-facing error transfer: a common representative index preserves a
quotient size bound and a complex trace-correlation bound, up to epsilon. -/
theorem select_coordinate_with_bounds (a ξ b : Sequences M)
    (d r ε : ℝ) (target : ℂ) (hε : 0 < ε)
    (ha : ‖sequenceQuotient τ ω a‖ ≤ d)
    (hb : ‖inner ℂ (sequenceInclusion τ ω ξ) (sequenceInclusion τ ω b) - target‖ ≤ r) :
    ∃ n : ℕ, τ.norm₂ (a n) < d + ε ∧ ‖τ.trace (star (ξ n)*b n)-target‖ < r+ε := by
  obtain ⟨n,hn,ht⟩ := select_coordinate τ ω a ξ b ε hε
  refine ⟨n, hn.trans_le (add_le_add ha le_rfl), ?_⟩
  have h := norm_sub_le_norm_sub_add_norm_sub (τ.trace (star (ξ n)*b n))
    (inner ℂ (sequenceInclusion τ ω ξ) (sequenceInclusion τ ω b)) target
  linarith

end Generator.Tracial

end

end OAI
