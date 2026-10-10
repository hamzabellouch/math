import OAI.Analysis.KadisonKastler.GraphResolventCompression
import OAI.Analysis.KadisonKastler.FrequencyCovariance
import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism
import OAI.Analysis.KadisonKastler.ModularConjugationData
import OAI.Analysis.KadisonKastler.ModularStateAction

namespace OAI

/-! # The published modular spectral resolution, in bounded coordinates

Blackadar, *Operator Algebras* (2006), III.4.3.2 and III.4.4.7--9
and III.4.6.1--2 (printed pp.313, 316--317, 320), gives the modular group, centralizer characterization and the polar
decomposition of the closed Tomita operator. III.4.7.1--2 (pp.325--326)
identifies its action by the KMS strip condition. I.7.4.5--7 and I.7.4.10
(pp.34--37) give its logarithmic spectral resolution and functional calculus.

We retain only the upper cuts of `log Δ`, their Fourier gauge identity,
and the bounded functional-calculus identities at distance `1/2` from a
cut. The first entry of the graph projection is `(1 + c² Δ)⁻¹`.
The identification of the second graph coordinate may be any antiunitary.
There is no comparison between two algebras in this published input.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The part of modular spectral theory used by the application. All
operators retained here are bounded, including the restricted inverse. -/
structure ModularSpectralResolution (M : VonNeumannAlgebra H) (Ω : H) where
  group : Multiplicative ℝ →* unitary (H →L[ℂ] H)
  continuous : ∀ x, Continuous (fun t : ℝ => (group (Multiplicative.ofAdd t) : H →L[ℂ] H) x)
  normalizes : ∀ t, Conjugates (group t) M M
  isModular : IsModularStateGroup M Ω group
  centralizer_fixed : ∀ x ∈ M, ProductStateCentralizes M Ω x →
    ∀ t, unitaryConj (group t) x = x
  upperCut : ℝ → H →L[ℂ] H
  projection : ∀ a, IsStarProjection (upperCut a)
  upper_contracts : ∀ a, ‖upperCut a‖ ≤ 1
  lower_contracts : ∀ a, ‖1 - upperCut a‖ ≤ 1
  measurable : ∀ a x, AEStronglyMeasurable (fun ξ : ℝ => upperCut (a - 2 * Real.pi * ξ) x) volume
  gauge_identity : ∀ a,
    (star (regularGauge group continuous) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularFrequencyProjection a *
        (regularGauge group continuous : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
        (regularFieldOperator volume (fun ξ => upperCut (a - 2 * Real.pi * ξ))
          (measurable a) 1 (Filter.Eventually.of_forall fun _ξ => upper_contracts _))
  high_inverse : ∀ (J : H ≃ₗᵢ⋆[ℂ] H) a, ∃ R : H →L[ℂ] H,
    ‖R‖ ≤ 1 + Real.exp (-(1 / 2 : ℝ)) ∧
    (1 - graphResolvent M J Ω (Real.exp (-a / 2))) * R = upperCut (a + 1 / 2) ∧
    upperCut (a + 1 / 2) * R = R
  low_bound : ∀ (J : H ≃ₗᵢ⋆[ℂ] H) a,
    ‖(1 - upperCut (a - 1 / 2)) * (1 - graphResolvent M J Ω (Real.exp (-a / 2)))‖ ≤
      Real.exp (-(1 / 2 : ℝ)) / (1 + Real.exp (-(1 / 2 : ℝ)))
  low_support : ∀ (J : H ≃ₗᵢ⋆[ℂ] H) a,
    (1 - upperCut (a - 1 / 2)) * (1 - graphResolvent M J Ω (Real.exp (-a / 2))) *
        (1 - upperCut (a - 1 / 2)) =
      (1 - upperCut (a - 1 / 2)) * (1 - graphResolvent M J Ω (Real.exp (-a / 2)))

/-- Tomita--Takesaki and the spectral theorem at a cyclic separating vector,
restricted to the bounded data above. -/
def PublishedModularSpectralResolution : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
    ∀ (M : VonNeumannAlgebra H) (Ω : H),
      DenseRange (algebraVectorMap M Ω) → Function.Injective (algebraVectorMap M Ω) →
      Nonempty (ModularConjugationData M Ω × ModularSpectralResolution M Ω)

end

end KadisonKastler

end OAI
