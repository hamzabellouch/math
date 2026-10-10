import OAI.Probability.InvariantIsing.Spectral.MeasureMagneticTransport
import OAI.Probability.InvariantIsing.Core.FiniteFieldLawCoupling

namespace OAI

/-! The finite-field magnetic value depends on the field law, not on its
choice of positive atomic labels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
namespace InvariantIsing

theorem measureMagnetic_eq_of_field_law_eq {A B : Type*} [Fintype A] [Fintype B]
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (γ c : A → ℝ) (δ d : B → ℝ) (hγ : ∀ i, 0 < γ i) (hδ : ∀ j, 0 < δ j)
    (hγsum : ∑ i, γ i=1) (hδsum : ∑ j, δ j=1)
    (he : finiteSpectralMeasure γ c=finiteSpectralMeasure δ d) :
    (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) γ c).toReal=
      (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) δ d).toReal := by
  have hmass := fieldAtomMass_eq_of_law_eq γ c δ d (fun i => (hγ i).le)
    (fun j => (hδ j).le) he
  have hh := measureMagnetic_transport_le ν a b hcompact hbound ha hb
    (sameFieldCoupling γ c δ d) γ c δ d
    (sameFieldCoupling_nonneg γ c δ d hγ (fun j => (hδ j).le))
    (fun i => (hγ i).le) hδ hγsum hδsum
    (sameFieldCoupling_row γ c δ d hγ hmass) (sameFieldCoupling_col γ c δ d hδ hmass)
  have hk := measureMagnetic_transport_le ν a b hcompact hbound ha hb
    (sameFieldCoupling δ d γ c) δ d γ c
    (sameFieldCoupling_nonneg δ d γ c hδ (fun i => (hγ i).le))
    (fun j => (hδ j).le) hγ hδsum hγsum
    (sameFieldCoupling_row δ d γ c hδ (fun x => (hmass x).symm))
    (sameFieldCoupling_col δ d γ c hγ (fun x => (hmass x).symm))
  rw [sameFieldCoupling_cost,add_zero] at hh hk
  exact le_antisymm hh hk

end InvariantIsing

end

end OAI
