import OAI.Analysis.KadisonSimilarity.Representation.FieldWeakClosure

namespace OAI

/-! Extend fields from a conull measurable base by zero while retaining
their actual L² action on the original measure space. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {Ω F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (μ : Measure Ω) (s : Set Ω)

def zeroExtendOperatorField (Q : s → F →L[ℂ] F) (x : Ω) : F →L[ℂ] F := by
  classical
  exact if h : x ∈ s then Q ⟨x, h⟩ else 0

theorem zeroExtendOperatorField_action (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (T : Lp F 2 μ →L[ℂ] Lp F 2 μ) (Q : s → F →L[ℂ] F)
    (hQ : ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ, T f x = Q x (f x)) :
    ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, T f x = zeroExtendOperatorField s Q x (f x) := by
  intro f
  have hmem : ∀ᵐ x ∂μ, x ∈ s := by
    rw [ae_iff]
    exact hnull
  have hr : ∀ᵐ x ∂μ.restrict s, T f x = zeroExtendOperatorField s Q x (f x) := by
    apply (ae_restrict_iff_subtype hs).mpr
    filter_upwards [hQ f] with x hx
    simpa only [zeroExtendOperatorField, dite_eq_left x.property] using hx
  filter_upwards [hmem, ae_imp_of_ae_restrict hr] with x hx hh
  exact hh hx

variable [CompleteSpace F]

omit [MeasurableSpace Ω] in
theorem zeroExtendOperatorField_mem
    (P : Ω → VonNeumannAlgebra F) (Q : s → F →L[ℂ] F)
    (hQ : ∀ x : s, Q x ∈ P x) :
    ∀ x, zeroExtendOperatorField s Q x ∈ P x := by
  intro x
  by_cases hx : x ∈ s
  · simpa only [zeroExtendOperatorField, dite_eq_left hx] using hQ ⟨x, hx⟩
  · simp only [zeroExtendOperatorField, dite_eq_right hx]
    exact (P x).toStarSubalgebra.zero_mem

end KadisonSimilarity

end

end OAI
