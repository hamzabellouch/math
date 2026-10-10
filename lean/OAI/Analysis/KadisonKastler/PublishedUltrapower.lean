import OAI.Analysis.KadisonKastler.ConcreteFiniteTrace

namespace OAI

/-! # The published tracial-ultraproduct construction

Popa, *Independence properties in subalgebras of ultraproduct II₁
factors*, J. Funct. Anal. 266 (2014), §1.6 (arXiv:1308.3982v3,
printed pp. 7–8), recalls the tracial ultraproduct as a finite von
Neumann algebra, with trace the ultralimit of the coordinate traces.
For a constant sequence of II₁ factors it is again a II₁ factor.

The input below contains exactly that construction. The two-norm kernel
property used by clipping is derived afterwards from faithfulness and
the trace formula; it is not an additional input.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- A represented tracial ultrapower, with the published coordinate
trace formula. The quotient is a concrete von Neumann algebra. -/
structure TracialUltrapower (τ : FaithfulTracialState B) (ω : Ultrafilter ℕ) where
  H : Type u
  [normedAddCommGroup : NormedAddCommGroup H]
  [innerProductSpace : InnerProductSpace ℂ H]
  [completeSpace : CompleteSpace H]
  algebra : VonNeumannAlgebra H
  factor : Generator.IsII1Factor algebra.toStarSubalgebra
  quotient : BoundedSequence B →⋆ₐ[ℂ] Algebra algebra
  surjective : Function.Surjective quotient
  trace_limit : ∀ x : BoundedSequence B,
    Tendsto (fun j => τ.toLinearMap (x j)) (ω : Filter ℕ)
      (𝓝 ((concreteFactorTrace factor).toLinearMap (quotient x)))

attribute [instance] TracialUltrapower.normedAddCommGroup
  TracialUltrapower.innerProductSpace TracialUltrapower.completeSpace

/-- The canonical faithful normal trace of the represented II₁ factor. -/
def TracialUltrapower.trace {τ : FaithfulTracialState B} {ω : Ultrafilter ℕ}
    (Q : TracialUltrapower τ ω) : FaithfulTracialState (Algebra Q.algebra) :=
  concreteFactorTrace Q.factor

/-- Popa §1.6, specialized to the constant sequence of the given II₁
factor with its already constructed faithful normal trace. -/
def PublishedTracialUltrapower : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (ω : Ultrafilter ℕ), (ω : Filter ℕ) ≤ atTop →
    Nonempty (TracialUltrapower (concreteFactorTrace hM) ω)

/-- The trace formula commutes with the squared tracial norm. -/
theorem TracialUltrapower.traceTwoNorm_sq_limit {τ : FaithfulTracialState B}
    {ω : Ultrafilter ℕ} (Q : TracialUltrapower τ ω) (x : BoundedSequence B) :
    Tendsto (fun j => traceTwoNorm τ (x j) ^ 2) (ω : Filter ℕ)
      (𝓝 (traceTwoNorm Q.trace (Q.quotient x) ^ 2)) := by
  have h := (Complex.continuous_re.tendsto _).comp (Q.trace_limit (star x * x))
  simpa only [Function.comp_def, TracialUltrapower.trace, BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.star_apply,
    map_mul, map_star, ← traceTwoNorm_sq] using h

/-- Faithfulness identifies the clipping kernel with the two-null
sequences. This is proved from the published trace formula. -/
theorem TracialUltrapower.isTraceQuotient {τ : FaithfulTracialState B}
    {ω : Ultrafilter ℕ} (Q : TracialUltrapower τ ω) :
    IsTraceQuotient τ (ω : Filter ℕ) Q.quotient := by
  intro x
  have h := Q.traceTwoNorm_sq_limit x
  constructor
  · intro hx
    rw [hx, traceTwoNorm, star_zero, zero_mul, map_zero, Complex.zero_re,
      Real.sqrt_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    have hs := (Real.continuous_sqrt.tendsto 0).comp h
    simpa only [Function.comp_def, Real.sqrt_sq (traceTwoNorm_nonneg τ _), Real.sqrt_zero] using hs
  · intro hx
    have hzero := hx.pow 2
    have he : traceTwoNorm Q.trace (Q.quotient x) ^ 2 = 0 := by
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using tendsto_nhds_unique h hzero
    have hr : (Q.trace.toLinearMap (star (Q.quotient x) * Q.quotient x)).re = 0 := by
      rwa [traceTwoNorm_sq] at he
    apply Q.trace.faithful
    apply Complex.ext
    · simpa only [Complex.zero_re] using hr
    · simpa only [Complex.zero_im] using Q.trace.positive_im (Q.quotient x)

end

end KadisonKastler

end OAI
