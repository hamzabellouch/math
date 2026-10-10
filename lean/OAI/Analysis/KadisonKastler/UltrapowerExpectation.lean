import OAI.Analysis.KadisonKastler.PublishedUltrapower
import OAI.Analysis.KadisonKastler.ConcreteWeakTransfer

namespace OAI

/-! # The actual expectation onto the constant copy

Weak compactness constructs the expectation value inside the original
von Neumann algebra. The finite-vector normal trace identifies it by
trace pairings. This constructs, rather than assumes, the expectation
used in the scalar-recovery weak limit.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : Type*} [CStarAlgebra B]

/-- Constant sequences as a unital star homomorphism. -/
def boundedSequenceConst : B →⋆ₐ[ℂ] BoundedSequence B where
  toFun := BoundedContinuousFunction.const ℕ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
theorem boundedSequenceConst_apply (b : B) (j : ℕ) : boundedSequenceConst b j = b := rfl

/-- A faithful tracial state separates elements by left pairings. -/
theorem eq_of_trace_left_pairings (τ : FaithfulTracialState B) {a b : B}
    (h : ∀ c, τ.toLinearMap (c * a) = τ.toLinearMap (c * b)) : a = b := by
  apply sub_eq_zero.mp
  apply τ.faithful
  rw [mul_sub, map_sub, h, sub_self]

/-- A trace-preserving star homomorphism out of a faithful tracial
algebra is injective. -/
theorem injective_of_trace_preserving {C : Type*} [CStarAlgebra C]
    (τ : FaithfulTracialState B) (σ : FaithfulTracialState C) (φ : B →⋆ₐ[ℂ] C)
    (hφ : ∀ x, σ.toLinearMap (φ x) = τ.toLinearMap x) : Function.Injective φ := by
  intro a b hab
  apply eq_of_trace_left_pairings τ
  intro c
  calc
    τ.toLinearMap (c * a) = σ.toLinearMap (φ (c * a)) := (hφ _).symm
    _ = σ.toLinearMap (φ c * φ a) := congrArg σ.toLinearMap (map_mul φ c a)
    _ = σ.toLinearMap (φ c * φ b) := congrArg (fun y => σ.toLinearMap (φ c * y)) hab
    _ = σ.toLinearMap (φ (c * b)) := congrArg σ.toLinearMap (map_mul φ c b).symm
    _ = τ.toLinearMap (c * b) := hφ _

/-- Bounded sequences admit a concrete weak limit with all trace
pairings, using the finite-vector formula. -/
theorem FiniteVectorTrace.exists_weak_limit_pairings
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}
    (hτ : FiniteVectorTrace τ) (ω : Ultrafilter ℕ) (s : BoundedSequence (Algebra M)) :
    ∃ a : Algebra M, ∀ b : Algebra M,
      Tendsto (fun j => τ.toLinearMap (b * s j)) (ω : Filter ℕ)
        (𝓝 (τ.toLinearMap (b * a))) := by
  obtain ⟨T, _, hT⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω
    (fun j => (s j : H →L[ℂ] H)) ‖s‖ (norm_nonneg s) s.norm_coe_le_norm
  let a : Algebra M := ⟨T, Generator.Tracial.weak_operator_limit_mem M s T hT⟩
  refine ⟨a, ?_⟩
  intro b
  apply hτ.tendsto (fun j => b * s j) (b * a)
  intro ξ η
  have h := hT ξ ((b : H →L[ℂ] H).adjoint η)
  simpa only [MulMemClass.coe_mul, mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_left] using h

/-- The trace formula and quotient map furnished by a tracial ultrapower.
The target trace is an explicit parameter so its construction stays separate
from the elementary expectation proofs. -/
structure TraceQuotientMap {C : Type*} [CStarAlgebra C]
    (τ : FaithfulTracialState B) (σ : FaithfulTracialState C) (ω : Ultrafilter ℕ) where
  quotient : BoundedSequence B →⋆ₐ[ℂ] C
  surjective : Function.Surjective quotient
  trace_limit : ∀ s, Tendsto (fun j => τ.toLinearMap (s j)) (ω : Filter ℕ)
    (𝓝 (σ.toLinearMap (quotient s)))

/-- The quotient trace formula passes to squared tracial two-norms. -/
theorem TraceQuotientMap.traceTwoNorm_sq_limit
    {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]
    {τA : FaithfulTracialState A} {τC : FaithfulTracialState C} {ω : Ultrafilter ℕ}
    (Q : TraceQuotientMap τA τC ω) (x : BoundedSequence A) :
    Tendsto (fun j => traceTwoNorm τA (x j) ^ 2) (ω : Filter ℕ)
      (𝓝 (traceTwoNorm τC (Q.quotient x) ^ 2)) := by
  have h := (Complex.continuous_re.tendsto _).comp (Q.trace_limit (star x * x))
  simpa only [Function.comp_def, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.star_apply, map_mul, map_star, ← traceTwoNorm_sq] using h

/-- Faithfulness identifies the exact two-null kernel of any such quotient. -/
theorem TraceQuotientMap.isTraceQuotient
    {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]
    {τA : FaithfulTracialState A} {τC : FaithfulTracialState C} {ω : Ultrafilter ℕ}
    (Q : TraceQuotientMap τA τC ω) : IsTraceQuotient τA (ω : Filter ℕ) Q.quotient := by
  intro x
  have h := Q.traceTwoNorm_sq_limit x
  constructor
  · intro hx
    rw [hx, traceTwoNorm, star_zero, zero_mul, map_zero, Complex.zero_re,
      Real.sqrt_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    have hs := (Real.continuous_sqrt.tendsto 0).comp h
    simpa only [Function.comp_def, Real.sqrt_sq (traceTwoNorm_nonneg τA _), Real.sqrt_zero]
      using hs
  · intro hx
    have hzero := hx.pow 2
    have he : traceTwoNorm τC (Q.quotient x) ^ 2 = 0 := by
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using tendsto_nhds_unique h hzero
    have hr : (τC.toLinearMap (star (Q.quotient x) * Q.quotient x)).re = 0 := by
      rwa [traceTwoNorm_sq] at he
    apply τC.faithful
    apply Complex.ext
    · simpa only [Complex.zero_re] using hr
    · simpa only [Complex.zero_im] using τC.positive_im (Q.quotient x)


namespace TraceQuotientMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}
variable {C : Type*} [CStarAlgebra C] {σ : FaithfulTracialState C}
variable {ω : Ultrafilter ℕ} (D : TraceQuotientMap τ σ ω)

/-- The actual constant copy of the original factor. -/
def constant : Algebra M →⋆ₐ[ℂ] C := D.quotient.comp boundedSequenceConst

/-- The constant copy preserves the constructed normalized trace. -/
theorem trace_constant (b : Algebra M) :
    σ.toLinearMap (D.constant (M := M) b) = τ.toLinearMap b := by
  exact tendsto_nhds_unique (D.trace_limit (boundedSequenceConst b)) tendsto_const_nhds

/-- Faithfulness of the constant embedding follows from its trace formula. -/
theorem constant_injective : Function.Injective (D.constant (M := M)) :=
  injective_of_trace_preserving τ σ (D.constant (M := M)) (D.trace_constant (M := M))

/-- Coordinate left pairings have the expected ultrapower trace limit. -/
theorem trace_pairing_limit (s : BoundedSequence (Algebra M)) (b : Algebra M) :
    Tendsto (fun j => τ.toLinearMap (b * s j)) (ω : Filter ℕ)
      (𝓝 (σ.toLinearMap (D.constant (M := M) b * D.quotient s))) := by
  have h := D.trace_limit (boundedSequenceConst b * s)
  have he : D.quotient (boundedSequenceConst b * s) =
      D.constant (M := M) b * D.quotient s :=
    map_mul D.quotient (boundedSequenceConst b) s
  rw [he] at h
  exact h

variable (hτ : FiniteVectorTrace τ)

include hτ

/-- Every ultrapower element has a representative of its trace pairings
in the original concrete factor. -/
theorem exists_expectation_value (x : C) :
    ∃ a : Algebra M, ∀ b : Algebra M,
      τ.toLinearMap (b * a) =
        σ.toLinearMap (D.constant (M := M) b * x) := by
  let s : BoundedSequence (Algebra M) := Classical.choose (D.surjective x)
  have hs : D.quotient s = x := Classical.choose_spec (D.surjective x)
  obtain ⟨a, ha⟩ := hτ.exists_weak_limit_pairings ω s
  refine ⟨a, fun b => ?_⟩
  have h := D.trace_pairing_limit (M := M) s b
  rw [hs] at h
  exact tendsto_nhds_unique (ha b) h

private def expectationValue (x : C) : Algebra M :=
  (D.exists_expectation_value (M := M) hτ x).choose

private theorem expectationValue_pairing (x : C) (b : Algebra M) :
    τ.toLinearMap (b * D.expectationValue hτ x) =
      σ.toLinearMap (D.constant (M := M) b * x) :=
  (D.exists_expectation_value (M := M) hτ x).choose_spec b

/-- The trace-preserving expectation, constructed by weak compactness. -/
def expectation : C →ₗ[ℂ] Algebra M where
  toFun := D.expectationValue hτ
  map_add' x y := by
    apply eq_of_trace_left_pairings τ
    intro b
    calc
      _ = σ.toLinearMap (D.constant (M := M) b * (x + y)) :=
        D.expectationValue_pairing hτ (x + y) b
      _ = σ.toLinearMap (D.constant (M := M) b * x) +
          σ.toLinearMap (D.constant (M := M) b * y) := by rw [mul_add, map_add]
      _ = τ.toLinearMap (b * D.expectationValue hτ x) +
          τ.toLinearMap (b * D.expectationValue hτ y) :=
        congrArg₂ (· + ·) (D.expectationValue_pairing hτ x b).symm
          (D.expectationValue_pairing hτ y b).symm
      _ = _ := by rw [mul_add, map_add]
  map_smul' c x := by
    apply eq_of_trace_left_pairings τ
    intro b
    calc
      _ = σ.toLinearMap (D.constant (M := M) b * (c • x)) :=
        D.expectationValue_pairing hτ (c • x) b
      _ = c • σ.toLinearMap (D.constant (M := M) b * x) :=
        by rw [mul_smul_comm, map_smul]
      _ = c • τ.toLinearMap (b * D.expectationValue hτ x) :=
        congrArg (c • ·) (D.expectationValue_pairing hτ x b).symm
      _ = _ := by simp only [mul_smul_comm, map_smul, RingHom.id_apply]

/-- The expectation's defining trace-pairing identity. -/
theorem expectation_pairing (x : C) (b : Algebra M) :
    τ.toLinearMap (b * D.expectation (M := M) hτ x) =
      σ.toLinearMap (D.constant (M := M) b * x) :=
  (D.exists_expectation_value (M := M) hτ x).choose_spec b

/-- The constructed expectation fixes the original algebra. -/
theorem expectation_constant (a : Algebra M) : D.expectation (M := M) hτ (D.constant (M := M) a) = a := by
  apply eq_of_trace_left_pairings τ
  intro b
  rw [D.expectation_pairing (M := M) hτ, ← map_mul, D.trace_constant (M := M)]

/-- The expectation preserves the trace. -/
theorem trace_expectation (x : C) :
    τ.toLinearMap (D.expectation (M := M) hτ x) = σ.toLinearMap x := by
  simpa only [one_mul, map_one] using D.expectation_pairing (M := M) hτ x 1

/-- In the ultrapower, the expectation is a linear projection onto the
range of the constant embedding. -/
def baseExpectation : C →ₗ[ℂ] C :=
  (D.constant (M := M)).toLinearMap.comp (D.expectation (M := M) hτ)

theorem baseExpectation_mem (x : C) :
    D.baseExpectation (M := M) hτ x ∈ (D.constant (M := M)).range := ⟨D.expectation (M := M) hτ x, rfl⟩

theorem baseExpectation_pairing (x b : C) (hb : b ∈ (D.constant (M := M)).range) :
    σ.toLinearMap (b * D.baseExpectation (M := M) hτ x) = σ.toLinearMap (b * x) := by
  obtain ⟨c, rfl⟩ := hb
  change σ.toLinearMap (D.constant (M := M) c * D.constant (M := M) (D.expectation (M := M) hτ x)) = _
  rw [← map_mul, D.trace_constant (M := M), D.expectation_pairing (M := M) hτ]
  rfl

/-- Each bounded representative converges weakly to the constructed
expectation in the original representation. -/
theorem weak_limit_expectation (s : BoundedSequence (Algebra M)) :
    ∀ ξ η : H, Tendsto (fun j => inner ℂ η ((s j : H →L[ℂ] H) ξ))
      (ω : Filter ℕ) (𝓝 (inner ℂ η ((D.expectation (M := M) hτ (D.quotient s) : H →L[ℂ] H) ξ))) := by
  apply hτ.weakOperator_ultralimit ω s
    (D.expectation (M := M) hτ (D.quotient s)) (norm_nonneg s) s.norm_coe_le_norm
  intro b
  have h := D.trace_limit (boundedSequenceConst b * s)
  rw [map_mul] at h
  simpa only [BoundedContinuousFunction.mul_apply, boundedSequenceConst_apply,
    constant, StarAlgHom.comp_apply, D.expectation_pairing (M := M) hτ] using h

/-- The expectation respects multiplication by the original algebra on
both sides. -/
theorem expectation_bimodule (a b : Algebra M) (x : C) :
    D.expectation (M := M) hτ (D.constant (M := M) a * x * D.constant (M := M) b) = a * D.expectation (M := M) hτ x * b := by
  apply eq_of_trace_left_pairings τ
  intro c
  calc
    _ = σ.toLinearMap (D.constant (M := M) c * (D.constant (M := M) a * x * D.constant (M := M) b)) :=
      D.expectation_pairing (M := M) hτ _ _
    _ = σ.toLinearMap (D.constant (M := M) (b * c * a) * x) := by
      simp only [map_mul]
      simpa only [mul_assoc] using σ.tracial (D.constant (M := M) c * D.constant (M := M) a * x) (D.constant (M := M) b)
    _ = τ.toLinearMap ((b * c * a) * D.expectation (M := M) hτ x) :=
      (D.expectation_pairing (M := M) hτ x (b * c * a)).symm
    _ = _ := by
      simpa only [mul_assoc] using
        τ.tracial b (c * a * D.expectation (M := M) hτ x)

/-- Every coordinate bound passes to the expectation. -/
theorem norm_expectation_quotient_le (s : BoundedSequence (Algebra M))
    {C : ℝ} (hC : 0 ≤ C) (hs : ∀ j, ‖s j‖ ≤ C) :
    ‖D.expectation (M := M) hτ (D.quotient s)‖ ≤ C := by
  obtain ⟨T, hTnorm, hT⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω
    (fun j => (s j : H →L[ℂ] H)) C hC hs
  have heq : (D.expectation (M := M) hτ (D.quotient s) : H →L[ℂ] H) = T := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply ext_inner_left ℂ
    intro η
    exact tendsto_nhds_unique (D.weak_limit_expectation (M := M) hτ s ξ η) (hT ξ η)
  change ‖(D.expectation (M := M) hτ (D.quotient s) : H →L[ℂ] H)‖ ≤ C
  rwa [heq]

/-- Quotient clipping upgrades the coordinate bound to contractivity in
the actual quotient operator norm. -/
theorem norm_expectation_le (x : C) : ‖D.expectation (M := M) hτ x‖ ≤ ‖x‖ := by
  let : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _
  let : PartialOrder (C) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (C) := CStarAlgebra.spectralOrderedRing _
  let : PartialOrder (BoundedSequence (Algebra M)) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (BoundedSequence (Algebra M)) := CStarAlgebra.spectralOrderedRing _
  apply le_of_forall_pos_le_add
  intro ε hε
  let s : BoundedSequence (Algebra M) := Classical.choose (D.surjective x)
  have hs : D.quotient s = x := Classical.choose_spec (D.surjective x)
  have hβ : 0 < ‖x‖ + ε := add_pos_of_nonneg_of_pos (norm_nonneg _) hε
  have hz : D.quotient (spectralClip (‖x‖ + ε) s) = x := by
    rw [map_spectralClip_eq D.quotient hβ s (by rw [hs]; linarith), hs]
  have hbound := D.norm_expectation_quotient_le (M := M) hτ
    (spectralClip (‖x‖ + ε) s) hβ.le (fun j => by
      rw [spectralClip_sequence_apply hβ]
      exact spectralClip_norm_le hβ _)
  simpa only [hz] using hbound

/-- The constructed expectation is a bounded linear map. -/
def expectationCLM : C →L[ℂ] Algebra M :=
  (D.expectation (M := M) hτ).mkContinuous 1 (fun x => by simpa only [one_mul] using D.norm_expectation_le (M := M) hτ x)

/-- The projection onto the constant copy is norm continuous. -/
def baseExpectationCLM : C →L[ℂ] C :=
  ((D.constant (M := M)).toLinearMap.mkContinuous 1 (fun x => by
    change ‖D.constant (M := M) x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le (D.constant (M := M)) x)).comp
      (D.expectationCLM (M := M) hτ)

end TraceQuotientMap

namespace TracialUltrapower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}
variable {ω : Ultrafilter ℕ}

/-- The published ultrapower supplies every premise of the constructed
expectation, with its canonical trace. -/
def traceQuotient (Q : TracialUltrapower τ ω) : TraceQuotientMap τ Q.trace ω where
  quotient := Q.quotient
  surjective := Q.surjective
  trace_limit s := by
    simpa only [TracialUltrapower.trace] using Q.trace_limit s

end TracialUltrapower

end

end KadisonKastler

end OAI
