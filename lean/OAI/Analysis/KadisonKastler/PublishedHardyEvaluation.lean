import OAI.Analysis.KadisonKastler.PositiveFrequencyAlgebra
import OAI.Analysis.KadisonKastler.MeasurablePoisson

namespace OAI

/-! # Published evaluation of causal Fourier multipliers

Kalle M. Mikkola, *Fourier multipliers for L² functions with values in
nonseparable Hilbert spaces and operator-valued Hᵖ boundary functions*,
Ann. Acad. Sci. Fenn. Math. 33 (2008), 121–130, Proposition 1.3 and
Theorem 1.5, pp.123–124. The Poisson representation is the Hardy-space
representation theorem cited in the proof of Corollary 1.7, p.125:
Rosenblum–Rovnyak, *Hardy Classes and Operator Theory* (1985),
Theorem 4.8B, p.90.

We retain only evaluation at one point, on the concrete algebra of
positive-frequency-preserving multiplication operators. Conjugation by
the Fourier transform identifies it with the causal translation-invariant
operators of Proposition 1.3 (a reflection interchanges Fourier signs).
That proposition gives the algebra representation; Theorem 1.5 identifies
the boundary field, and Poisson representation identifies its evaluation.
No holomorphic function space, norm estimate, perturbation conclusion or
choice of analytic approximant is included in this input.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

/-- The point-evaluation consequence of the published Hardy multiplier
representation. The domain and the Poisson integral are concrete. -/
def PublishedHardyMultiplierEvaluation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
    ∀ (t r : ℝ), 0 < r →
      ∃ ev : positiveFrequencyAlgebra (H := H) →ₐ[ℂ] (H →L[ℂ] H),
        ∀ (F : ℝ → H →L[ℂ] H)
          (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
          (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
          (T : positiveFrequencyAlgebra (H := H)),
          RepresentsOperatorField volume F T.val →
          ∀ hr : 0 < r, ev T = measurablePoissonAverage F hF C hC t r hr

end

end KadisonKastler

end OAI
