import OAI.Analysis.KadisonKastler.RegularCoreCharacters
import OAI.Analysis.KadisonKastler.RegularCoreFields

namespace OAI

/-! # Published spectral and diagonal decomposition inputs

The two inputs are kept separate. Blackadar, *Operator Algebras* (2006),
I.7.4.5--7 and I.7.4.10 (printed pp.35--37), gives the spectral-commutant
consequence of Stone's theorem: the commutant of multiplication by
`exp(i a t)`, for all real `a`, commutes with every bounded Borel multiplier.
Here the generator is multiplication by the coordinate `t`.

III.1.6.2--3 (printed pp.253--254) gives the diagonal-commutant decomposition
on the standard trivial field over the real line. Its conclusion is only
the existence of a measurable bounded operator field representing an
operator. Neither input asserts a core or fixed-point identification.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual multiplication operator associated to a bounded Borel
scalar function on the real line. -/
def regularScalarMultiplier (φ : ℝ → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  regularFieldOperator volume (fun t => φ t • (1 : H →L[ℂ] H))
    (fun ξ => hφ.aestronglyMeasurable.smul_const ξ) C
    (Filter.Eventually.of_forall fun t => by
      apply le_trans _ (hC t)
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro ξ
      simp only [smul_apply, one_apply_eq_self, norm_smul]
      exact le_rfl)

/-- Stone's spectral-commutant theorem, restricted to the concrete
character multiplication group on the real line. -/
def PublishedRealSpectralCommutant : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H,
      (∀ a : ℝ, Commute T (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) →
      ∀ (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C),
        Commute T (regularScalarMultiplier (H := H) φ hφ C hC)

/-- The diagonal-commutant decomposition theorem on a separable constant
Hilbert field over Lebesgue measure. -/
def PublishedRealDiagonalDecomposition : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
    ∀ T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H,
      (∀ (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C),
        Commute T (regularScalarMultiplier (H := H) φ hφ C hC)) →
      ∃ F : ℝ → H →L[ℂ] H,
        (∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume) ∧
        (∀ᵐ t ∂volume, ‖F t‖ ≤ ‖T‖) ∧ RepresentsOperatorField volume F T

end

end KadisonKastler

end OAI
