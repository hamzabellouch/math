import OAI.Analysis.KadisonKastler.PublishedFock
import OAI.Analysis.KadisonKastler.SpectralClipping
import OAI.Analysis.KadisonKastler.ClippedLimits
import Mathlib.Topology.ContinuousMap.Bounded.Star

namespace OAI

/-!
# Bounded sequences, spectral clipping and trace-to-strong transfer

The sequence algebra is the ordinary C*-algebra of bounded functions on
the discrete natural numbers. Evaluation commutes with the spectral
cutoff. A trace quotient therefore kills the discarded part as soon as
the quotient norm satisfies the desired cutoff bound.
-/

namespace KadisonKastler

open Filter
open scoped Topology BoundedContinuousFunction

noncomputable section

abbrev BoundedSequence (B : Type*) [CStarAlgebra B] := ℕ →ᵇ B

instance boundedSequenceCStarAlgebra {B : Type*} [CStarAlgebra B] :
    CStarAlgebra (BoundedSequence B) where

def boundedSequenceEval {B : Type*} [CStarAlgebra B] (j : ℕ) :
    BoundedSequence B →⋆ₐ[ℂ] B where
  toFun x := x j
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
theorem boundedSequenceEval_apply {B : Type*} [CStarAlgebra B]
    (j : ℕ) (x : BoundedSequence B) : boundedSequenceEval j x = x j := rfl

section Clipping

variable {B Q : Type*} [CStarAlgebra B] [CStarAlgebra Q]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder Q] [StarOrderedRing Q]

local instance sequenceOrder : PartialOrder (BoundedSequence B) := CStarAlgebra.spectralOrder _
local instance sequenceStarOrder : StarOrderedRing (BoundedSequence B) :=
  CStarAlgebra.spectralOrderedRing _

/-- The algebraic spectral clip evaluates to the clip of each coordinate. -/
theorem spectralClip_sequence_apply {β : ℝ} (hβ : 0 < β)
    (x : BoundedSequence B) (j : ℕ) :
    spectralClip β x j = spectralClip β (x j) :=
  map_spectralClip (boundedSequenceEval j) hβ x

omit [PartialOrder B] [StarOrderedRing B] in
/-- Clipping a bounded sequence at a bound for its quotient norm changes
it by an element of the quotient kernel. -/
theorem sequence_discard_quotient_zero (π : BoundedSequence B →⋆ₐ[ℂ] Q)
    {β : ℝ} (hβ : 0 < β) (x : BoundedSequence B) (hx : ‖π x‖ ≤ β) :
    π (x - spectralClip β x) = 0 :=
  map_sub_spectralClip_eq_zero π hβ x hx

end Clipping

/-- The tracial two-seminorm, on the faithful tracial algebra in use. -/
def traceTwoNorm {B : Type*} [CStarAlgebra B] (τ : FaithfulTracialState B) (x : B) : ℝ :=
  Real.sqrt ((τ.toLinearMap (star x * x)).re)

/-- Continuity from the tracial two-norm to the strong topology on each
norm-bounded ball. This is the exact normal-representation property used
by the clipping argument; no existence assertion is made here. -/
def TraceStrongContinuous {B H : Type*} [CStarAlgebra B]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : FaithfulTracialState B) (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ z : H, ∀ C : ℝ, 0 ≤ C → ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ ∀ x : B, ‖x‖ ≤ C → traceTwoNorm τ x < η → ‖ρ x z‖ < ε

/-- The continuity property transfers two-small bounded sequences to
strongly small sequences in the given representation. -/
theorem TraceStrongContinuous.tendsto {B H J : Type*} [CStarAlgebra B]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {τ : FaithfulTracialState B} {ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (hρ : TraceStrongContinuous τ ρ) (l : Filter J) (x : J → B)
    {C : ℝ} (hC : 0 ≤ C) (hx : ∀ j, ‖x j‖ ≤ C)
    (h2 : Tendsto (fun j => traceTwoNorm τ (x j)) l (𝓝 0)) (z : H) :
    Tendsto (fun j => ρ (x j) z) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨η, hη, hηx⟩ := hρ z C hC ε hε
  filter_upwards [h2.eventually (gt_mem_nhds hη)] with j hj
  simpa only [dist_zero_right] using hηx (x j) (hx j) hj

/-- The precise quotient-kernel condition needed for discarded sequences. -/
def IsTraceQuotient {B Q : Type*} [CStarAlgebra B] [CStarAlgebra Q]
    (τ : FaithfulTracialState B) (l : Filter ℕ)
    (π : BoundedSequence B →⋆ₐ[ℂ] Q) : Prop :=
  ∀ x, π x = 0 ↔ Tendsto (fun j => traceTwoNorm τ (x j)) l (𝓝 0)

/-- A zero quotient class acts strongly as zero in every representation
with the trace continuity property. -/
theorem IsTraceQuotient.strong_zero {B Q H : Type*} [CStarAlgebra B] [CStarAlgebra Q]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {τ : FaithfulTracialState B} {l : Filter ℕ}
    {π : BoundedSequence B →⋆ₐ[ℂ] Q} (hπ : IsTraceQuotient τ l π)
    {ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (hρ : TraceStrongContinuous τ ρ)
    (x : BoundedSequence B) (hx : π x = 0) (z : H) :
    Tendsto (fun j => ρ (x j) z) l (𝓝 0) :=
  hρ.tendsto l (fun j => x j) (norm_nonneg x) (x.norm_coe_le_norm) ((hπ x).mp hx) z

section DiscardedLimits

variable {B Q H : Type*} [CStarAlgebra B] [CStarAlgebra Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder Q] [StarOrderedRing Q]

local instance discardedSequenceOrder : PartialOrder (BoundedSequence B) :=
  CStarAlgebra.spectralOrder _
local instance discardedSequenceStarOrder : StarOrderedRing (BoundedSequence B) :=
  CStarAlgebra.spectralOrderedRing _

/-- Quotient clipping gives the actual strong error on every fixed vector. -/
theorem IsTraceQuotient.spectralDiscard_strong_zero
    {τ : FaithfulTracialState B} {l : Filter ℕ}
    {π : BoundedSequence B →⋆ₐ[ℂ] Q} (hπ : IsTraceQuotient τ l π)
    {ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (hρ : TraceStrongContinuous τ ρ)
    {β : ℝ} (hβ : 0 < β) (x : BoundedSequence B) (hx : ‖π x‖ ≤ β) (z : H) :
    Tendsto (fun j => ρ (x j - spectralClip β (x j)) z) l (𝓝 0) := by
  have hz := sequence_discard_quotient_zero π hβ x hx
  have ht := hπ.strong_zero hρ (x - spectralClip β x) hz z
  simpa only [BoundedContinuousFunction.sub_apply, spectralClip_sequence_apply hβ] using ht

/-- Right multiplication by any bounded sequence keeps the discarded
part in the kernel. This is the moving-vector transfer needed before
estimating the remaining unitary commutator. -/
theorem IsTraceQuotient.spectralDiscard_mul_strong_zero
    {τ : FaithfulTracialState B} {l : Filter ℕ}
    {π : BoundedSequence B →⋆ₐ[ℂ] Q} (hπ : IsTraceQuotient τ l π)
    {ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (hρ : TraceStrongContinuous τ ρ)
    {β : ℝ} (hβ : 0 < β) (x v : BoundedSequence B) (hx : ‖π x‖ ≤ β) (z : H) :
    Tendsto (fun j => ρ (x j - spectralClip β (x j)) (ρ (v j) z)) l (𝓝 0) := by
  have hz : π ((x - spectralClip β x) * v) = 0 := by
    rw [map_mul, sequence_discard_quotient_zero π hβ x hx, zero_mul]
  have ht := hπ.strong_zero hρ ((x - spectralClip β x) * v) hz z
  simpa only [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.sub_apply,
    spectralClip_sequence_apply hβ, map_mul, mul_apply_eq_comp] using ht

end DiscardedLimits

end

end KadisonKastler

end OAI
