import Mathlib.Analysis.InnerProductSpace.Completion
import OAI.Analysis.FactorGeneration.Ultrapower

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual trace Hilbert completion of the bounded-sequence tracial quotient.
The vector-trace representation is explicit data; its existence for an arbitrary
factor is not asserted here. No free-independence premise occurs. -/
open Filter
open scoped Topology ComplexConjugate
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

abbrev Q := TracialQuotient τ (ω : Filter ℕ)

@[simp] theorem trace_add (a b : Q τ ω) :
    quotientTrace τ ω (a+b) = quotientTrace τ ω a + quotientTrace τ ω b := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      apply tendsto_nhds_unique (traceRep_tendsto τ ω (a+b))
      change Tendsto (fun n => τ.trace (a.val n + b.val n)) _
        (𝓝 (traceRep τ ω a + traceRep τ ω b))
      simpa only [TracialRepresentation.trace_add] using
        (traceRep_tendsto τ ω a).add (traceRep_tendsto τ ω b)

@[simp] theorem trace_smul (c : ℂ) (a : Q τ ω) :
    quotientTrace τ ω (c • a) = c * quotientTrace τ ω a := by
  induction a using Quotient.inductionOn with
  | h a =>
    apply tendsto_nhds_unique (traceRep_tendsto τ ω (c • a))
    change Tendsto (fun n => τ.trace (c • a.val n)) _ (𝓝 (c * traceRep τ ω a))
    simpa only [TracialRepresentation.trace_smul] using
      (traceRep_tendsto τ ω a).const_mul c

def traceLinear : Q τ ω →ₗ[ℂ] ℂ where
  toFun := quotientTrace τ ω
  map_add' := trace_add τ ω
  map_smul' := trace_smul τ ω

theorem trace_pair (a b : M.toStarSubalgebra) :
    τ.trace (star a*b) = inner ℂ ((a : H →L[ℂ] H) τ.vector)
      ((b : H →L[ℂ] H) τ.vector) := by
  unfold TracialRepresentation.trace
  change inner ℂ τ.vector ((star (a : H →L[ℂ] H)) ((b : H →L[ℂ] H) τ.vector)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem trace_pair_conj (a b : Q τ ω) :
    star (quotientTrace τ ω (star b*a)) = quotientTrace τ ω (star a*b) := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      change star (traceRep τ ω (star b*a)) = traceRep τ ω (star a*b)
      apply tendsto_nhds_unique ((traceRep_tendsto τ ω (star b*a)).star)
      have ht := traceRep_tendsto τ ω (star a*b)
      change Tendsto (fun n => τ.trace (star (a.val n)*b.val n)) _ _ at ht
      change Tendsto (fun n => star (τ.trace (star (b.val n)*a.val n))) _ _
      convert ht using 1
      funext n
      simp only [trace_pair]
      exact inner_conj_symm _ _

theorem trace_square_nonneg (a : Q τ ω) :
    0 ≤ (quotientTrace τ ω (star a*a)).re := by
  induction a using Quotient.inductionOn with
  | h a =>
    have ht := Complex.continuous_re.continuousAt.tendsto.comp (traceRep_tendsto τ ω (star a*a))
    change 0 ≤ (traceRep τ ω (star a*a)).re
    apply ge_of_tendsto ht
    exact Eventually.of_forall (fun n => by
      change 0 ≤ (τ.trace (star (a.val n)*a.val n)).re
      rw [τ.trace_star_mul]
      simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using sq_nonneg (τ.norm₂ (a.val n)))

/-- The quotient two-norm is the ultralimit of the coordinate two-norms. -/
theorem norm₂_tendsto (a : Bounded M) :
    Tendsto (fun n => τ.norm₂ (a.val n)) (ω : Filter ℕ)
      (𝓝 (Real.sqrt (quotientTrace τ ω (star (quotientMap τ (ω : Filter ℕ) a) *
        quotientMap τ (ω : Filter ℕ) a)).re)) := by
  change Tendsto (fun n => τ.norm₂ (a.val n)) (ω : Filter ℕ)
    (𝓝 (Real.sqrt (traceRep τ ω (star a*a)).re))
  have ht := (Complex.continuous_re.continuousAt.tendsto.comp (traceRep_tendsto τ ω (star a*a))).sqrt
  convert ht using 1
  funext n
  change τ.norm₂ (a.val n) = Real.sqrt (τ.trace (star (a.val n)*a.val n)).re
  rw [τ.trace_star_mul, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact (Real.sqrt_sq (show 0 ≤ τ.norm₂ (a.val n) from norm_nonneg _)).symm

theorem trace_square_faithful (a : Q τ ω)
    (ha : quotientTrace τ ω (star a*a) = 0) : a = 0 := by
  induction a using Quotient.inductionOn with
  | h a =>
    change quotientMap τ (ω : Filter ℕ) a = quotientMap τ (ω : Filter ℕ) 0
    apply (quotientMap_eq_iff τ (ω : Filter ℕ) a 0).mpr
    have ht := norm₂_tendsto τ ω a
    change quotientTrace τ ω (star (quotientMap τ (ω : Filter ℕ) a) *
      quotientMap τ (ω : Filter ℕ) a) = 0 at ha
    simpa [TraceRel, ha] using ht

/-- The norm here is the trace norm, not the operator norm. -/
@[instance_reducible] def quotientInnerCore : InnerProductSpace.Core ℂ (Q τ ω) where
  inner a b := quotientTrace τ ω (star a*b)
  conj_inner_symm := trace_pair_conj τ ω
  re_inner_nonneg := trace_square_nonneg τ ω
  add_left a b c := by simp only [star_add, add_mul, trace_add]
  smul_left a b c := by simp only [star_smul, smul_mul_assoc, trace_smul]; rfl
  definite := trace_square_faithful τ ω

instance quotientNormedAddCommGroup : NormedAddCommGroup (Q τ ω) :=
  (quotientInnerCore τ ω).toNormedAddCommGroup
instance quotientInnerProductSpace : InnerProductSpace ℂ (Q τ ω) :=
  .ofCore { quotientInnerCore τ ω with }

@[simp] theorem inner_eq_trace (a b : Q τ ω) :
    inner ℂ a b = quotientTrace τ ω (star a*b) := rfl

/-- Genuine complete complex Hilbert space for the quotient trace. -/
abbrev L2 := UniformSpace.Completion (Q τ ω)

def inclusion : Q τ ω →ₗᵢ[ℂ] L2 τ ω :=
  UniformSpace.Completion.toComplₗᵢ

@[simp] theorem inclusion_inner (a b : Q τ ω) :
    inner ℂ (inclusion τ ω a) (inclusion τ ω b) = quotientTrace τ ω (star a*b) := by
  exact UniformSpace.Completion.inner_coe (𝕜 := ℂ) a b

theorem inclusion_injective : Function.Injective (inclusion τ ω) :=
  (inclusion τ ω).injective

end

/-! Centering actual bounded representatives changes no centered quotient
class. Every such class is a nonzero scalar multiple of a coordinatewise
centered contraction representative. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def boundedScalarTrace (a : Bounded M) : Bounded M :=
  ⟨fun j => τ.trace (a.val j) • (1 : M.toStarSubalgebra),by
    obtain ⟨C,hC,ha⟩ := a.property
    refine ⟨C,hC,fun j => ?_⟩
    rw [norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg _) operator_norm_one_le).trans
      (((τ.norm_trace_le_norm₂ _).trans (τ.norm₂_le_norm _)).trans (ha j))⟩

def boundedCenter (a : Bounded M) : Bounded M := a-boundedScalarTrace τ a

theorem boundedCenter_trace (a : Bounded M) (j : ℕ) :
    τ.trace ((boundedCenter τ a).val j)=0 := by
  change τ.trace (a.val j - τ.trace (a.val j) • 1)=0
  simp only [TracialRepresentation.trace_sub,TracialRepresentation.trace_smul,τ.trace_one,
    mul_one,sub_self]

theorem boundedCenter_quotient (ω : Ultrafilter ℕ) (a : Bounded M)
    (ha : quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) a)=0) :
    quotientMap τ (ω : Filter ℕ) (boundedCenter τ a)=quotientMap τ (ω : Filter ℕ) a := by
  apply (quotientMap_eq_iff τ (ω : Filter ℕ) _ _).mpr
  have ht := (traceRep_tendsto τ ω a).norm
  change traceRep τ ω a=0 at ha
  rw [ha,norm_zero] at ht
  change Tendsto (fun j => τ.norm₂ ((a.val j-τ.trace (a.val j) • 1)-a.val j)) _ _
  have he (j : ℕ) : (a.val j-τ.trace (a.val j) • 1)-a.val j =
      -(τ.trace (a.val j) • (1 : M.toStarSubalgebra)) := by abel
  have hn (j : ℕ) : τ.norm₂ (-(τ.trace (a.val j) • (1 : M.toStarSubalgebra))) =
      ‖τ.trace (a.val j)‖ := by
    change ‖-(τ.trace (a.val j) • τ.vector)‖ = _
    rw [norm_neg,norm_smul,τ.norm_vector,mul_one]
  simpa only [he,hn] using ht

theorem exists_centered_contraction_representative (ω : Ultrafilter ℕ)
    (q : TracialQuotient τ (ω : Filter ℕ)) (hq : quotientTrace τ ω q=0) :
    ∃ c : ℂ,c ≠ 0 ∧ ∃ b : Bounded M,
      (∀ j,‖b.val j‖ ≤ 1) ∧ (∀ j,τ.trace (b.val j)=0) ∧
      q=c • quotientMap τ (ω : Filter ℕ) b := by
  obtain ⟨a,rfl⟩ := quotientMap_surjective τ (ω : Filter ℕ) q
  obtain ⟨C,hC,hbound⟩ := (boundedCenter τ a).property
  let r : ℝ := C+1
  have hr : 0 < r := by dsimp [r]; linarith
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  refine ⟨(r : ℂ),hrc,(r : ℂ)⁻¹ • boundedCenter τ a,?_,?_,?_⟩
  · intro j
    change ‖(r : ℂ)⁻¹ • (boundedCenter τ a).val j‖ ≤ 1
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    apply (inv_mul_le_iff₀ hr).mpr
    simpa only [mul_one] using (hbound j).trans (by dsimp [r]; linarith)
  · intro j
    change τ.trace ((r : ℂ)⁻¹ • (boundedCenter τ a).val j)=0
    rw [TracialRepresentation.trace_smul,boundedCenter_trace,mul_zero]
  · rw [quotientMap_smul,smul_smul,mul_inv_cancel₀ hrc,one_smul,
      boundedCenter_quotient τ ω a hq]

end

/-! Trace Cauchy–Schwarz and unitary invariance on the tracial quotient. -/
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[simp] theorem quotient_norm_one : ‖(1 : Q τ ω)‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_eq_trace, star_one, one_mul, quotientTrace_one]
  norm_num

@[simp] theorem quotient_norm_star (a : Q τ ω) : ‖star a‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    inner_eq_trace, inner_eq_trace, star_star, quotientTrace_mul_comm τ ω a (star a)]

@[simp] theorem quotient_trace_sub (a b : Q τ ω) :
    quotientTrace τ ω (a-b) = quotientTrace τ ω a-quotientTrace τ ω b :=
  (traceLinear τ ω).map_sub a b

theorem quotient_norm_mul_unitary (a u : Q τ ω) (hu : u*star u = 1) :
    ‖a*u‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    inner_eq_trace, inner_eq_trace, star_mul]
  have he : quotientTrace τ ω (star u*star a*(a*u)) = quotientTrace τ ω (star a*a) := by
    rw [mul_assoc, quotientTrace_mul_comm τ ω (star u) (star a*(a*u))]
    simp only [mul_assoc, hu, mul_one]
  rw [he]

theorem quotient_trace_cauchy_schwarz (a b : Q τ ω) :
    ‖quotientTrace τ ω (star a*b)‖ ≤ ‖a‖*‖b‖ :=
  norm_inner_le_norm a b

/-- The source's complex trace error bound from its actual first-order identity
and the actual quotient remainder, with unitary right multiplication accounted for. -/
theorem quotient_correlation_remainder (ξ v c w : Q τ ω) (target : ℂ) (R : ℝ)
    (hw : w*star w = 1)
    (hfirst : quotientTrace τ ω (star ξ*((1+c)*w)) = target)
    (hrem : ‖v-(1+c)‖ ≤ R) :
    ‖quotientTrace τ ω (star ξ*(v*w))-target‖ ≤ ‖ξ‖*R := by
  have he : quotientTrace τ ω (star ξ*(v*w))-target =
      quotientTrace τ ω (star ξ*((v-(1+c))*w)) := by
    rw [← hfirst, sub_mul, mul_sub, quotient_trace_sub]
  rw [he]
  apply (quotient_trace_cauchy_schwarz τ ω ξ _).trans
  rw [quotient_norm_mul_unitary τ ω _ w hw]
  exact mul_le_mul_of_nonneg_left hrem (norm_nonneg ξ)

end Generator.Tracial

end

end OAI
