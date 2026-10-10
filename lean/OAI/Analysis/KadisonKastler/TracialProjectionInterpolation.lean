import OAI.Analysis.KadisonKastler.TracialProjectionConjugacy
import OAI.Analysis.FactorGeneration.ProjectionLimits

namespace OAI

/-! # Interpolating a projection inside one diagonal slot -/

namespace KadisonKastler

open Generator.Tracial UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- If the trace of p lies between that of q and q+d, cut just the orthogonal
slot d. The resulting projection has exactly the trace of p and hence is
unitarily conjugate to p in the original finite factor. -/
theorem exists_tracial_projection_interpolation (τ : TracialRepresentation M)
    (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (p q d : AlgebraProjection M) (hqd : q.val * d.val = 0)
    (hlo : (τ.trace q.val).re ≤ (τ.trace p.val).re)
    (hhi : (τ.trace p.val).re ≤ (τ.trace q.val).re + (τ.trace d.val).re) :
    ∃ (s : AlgebraProjection M) (u : unitary (Algebra M)),
      q ≤ s ∧ s ≤ (⟨q.val + d.val, q.property.add d.property hqd⟩ : AlgebraProjection M) ∧
      (u : Algebra M) * s.val * star (u : Algebra M) = p.val := by
  obtain ⟨t, ht, hdt, htd, htt⟩ := exists_exact_trace_subprojection τ hdiff d.val d.property
    ((τ.trace p.val).re - (τ.trace q.val).re) (sub_nonneg.mpr hlo) (by linarith)
  have hqt : q.val * t = 0 := by
    calc
      q.val * t = q.val * (d.val * t) := by rw [hdt]
      _ = 0 := by rw [← mul_assoc, hqd, zero_mul]
  have htq : t * q.val = 0 := by
    simpa only [star_mul, ht.isSelfAdjoint.star_eq, q.property.isSelfAdjoint.star_eq,
      star_zero] using congrArg star hqt
  let s : AlgebraProjection M := ⟨q.val + t, q.property.add ht hqt⟩
  have hqs : q ≤ s := by
    change (q.val + t) * q.val = q.val
    rw [add_mul, q.property.isIdempotentElem.eq, htq, add_zero]
  have hsq : s ≤ (⟨q.val + d.val, q.property.add d.property hqd⟩ : AlgebraProjection M) := by
    change (q.val + d.val) * (q.val + t) = q.val + t
    have hdq := PartialIsometry.orthogonal_reverse q d hqd
    rw [add_mul, mul_add, mul_add, q.property.isIdempotentElem.eq, hqt, hdq, hdt]
    simp only [add_zero, zero_add]
  have htrace : τ.trace s.val = τ.trace p.val := by
    change τ.trace (q.val + t) = τ.trace p.val
    rw [τ.trace_add, htt, Complex.ofReal_sub, ← add_sub_assoc]
    calc
      τ.trace q.val + ((τ.trace p.val).re : ℂ) - ((τ.trace q.val).re : ℂ) =
          ((τ.trace p.val).re : ℂ) := by
        rw [projection_trace_real τ q]
        simp only [Complex.ofReal_re]
        abel
      _ = τ.trace p.val := (projection_trace_real τ p).symm

  obtain ⟨u, hu⟩ := exists_tracial_projection_conjugacy τ hfactor s p htrace
  exact ⟨s, u, hqs, hsq, hu⟩

end

end KadisonKastler

end OAI
