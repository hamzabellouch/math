import OAI.Analysis.KadisonSimilarity.Representation.BoundedMeasurableField
import OAI.Analysis.KadisonSimilarity.Representation.FiberCommutant

namespace OAI

/-! # Reconstructing operators in a represented bicommutant

If scalar localizations belong to a represented von Neumann algebra, every
operator in its commutant has an actual measurable field. The fiber
commutant theorem then shows that a bounded measurable field in the fiber
bicommutants reconstructs an operator in the original bicommutant.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter

variable {Ω H A : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]

/-- A bounded measurable field in the genuine fiber bicommutants gives an
operator in the global bicommutant. The localization hypothesis is ordinary
membership of the scalar multiplication projections. -/
theorem boundedFieldOperator_mem_representationVonNeumannAlgebra
    (σ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (ρ : ∀ _a : Ω, A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b : A, ∀ f : Lp H 2 μ,
      ∀ᵐ a ∂μ, σ b f a = ρ a b (f a))
    (hlocal : ∀ (s : Set Ω) (hs : MeasurableSet s),
      l2Localization μ s hs ∈ representationVonNeumannAlgebra σ)
    (Q : Ω → H →L[ℂ] H)
    (hmeas : ∀ x : H, AEStronglyMeasurable (fun a => Q a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖Q a‖ ≤ C)
    (hmem : ∀ᵐ a ∂μ, Q a ∈ representationVonNeumannAlgebra (ρ a)) :
    boundedFieldOperator μ Q hmeas C hbound ∈ representationVonNeumannAlgebra σ := by
  rw [← (representationVonNeumannAlgebra σ).commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  have hTlocal : ∀ (s : Set Ω) (hs : MeasurableSet s),
      T * l2Localization μ s hs = l2Localization μ s hs * T :=
    fun s hs => (VonNeumannAlgebra.mem_commutant_iff.mp hT _ (hlocal s hs)).symm
  let R := diagonalField μ T hTlocal
  have hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a) :=
    diagonalField_action μ T hTlocal
  have hTσ : ∀ b : A, T * σ b = σ b * T := fun b =>
    (VonNeumannAlgebra.mem_commutant_iff.mp hT _
      (mem_representationVonNeumannAlgebra σ b)).symm
  have hcomm : ∀ᵐ a ∂μ, Q a * R a = R a * Q a := by
    filter_upwards [hmem,
      ae_mem_fiber_representation_commutant μ σ ρ T R hσ hR hTσ] with a hq hr
    exact VonNeumannAlgebra.mem_commutant_iff.mp hr _ hq
  exact (boundedFieldOperator_commutes_of_ae μ Q hmeas C hbound T R hR hcomm).symm

/-- The reconstruction needs genuine representations only on a measurable
conull base. A global field can have any values on its null complement. -/
theorem boundedFieldOperator_mem_of_restricted_fiber_bicommutants
    (s : Set Ω) (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (σ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (ρ : ∀ _a : s, A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b : A, ∀ f : Lp H 2 μ,
      ∀ᵐ a : s ∂Measure.comap ((↑) : s → Ω) μ, σ b f a = ρ a b (f a))
    (hlocal : ∀ (t : Set Ω) (ht : MeasurableSet t),
      l2Localization μ t ht ∈ representationVonNeumannAlgebra σ)
    (Q : Ω → H →L[ℂ] H)
    (hmeas : ∀ x : H, AEStronglyMeasurable (fun a => Q a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖Q a‖ ≤ C)
    (hmem : ∀ᵐ a : s ∂Measure.comap ((↑) : s → Ω) μ,
      Q a ∈ representationVonNeumannAlgebra (ρ a)) :
    boundedFieldOperator μ Q hmeas C hbound ∈ representationVonNeumannAlgebra σ := by
  rw [← (representationVonNeumannAlgebra σ).commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  have hTlocal : ∀ (t : Set Ω) (ht : MeasurableSet t),
      T * l2Localization μ t ht = l2Localization μ t ht * T :=
    fun t ht => (VonNeumannAlgebra.mem_commutant_iff.mp hT _ (hlocal t ht)).symm
  let R := diagonalField μ T hTlocal
  have hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a) :=
    diagonalField_action μ T hTlocal
  have hTσ : ∀ b : A, T * σ b = σ b * T := fun b =>
    (VonNeumannAlgebra.mem_commutant_iff.mp hT _
      (mem_representationVonNeumannAlgebra σ b)).symm
  have hcommOn : ∀ᵐ a : s ∂Measure.comap ((↑) : s → Ω) μ,
      Q a * R a = R a * Q a := by
    filter_upwards [hmem, ae_mem_restricted_fiber_representation_commutant
      μ s hs σ ρ T R hσ hR hTσ] with a hq hr
    exact VonNeumannAlgebra.mem_commutant_iff.mp hr _ hq
  have hcomm : ∀ᵐ a ∂μ, Q a * R a = R a * Q a := by
    have hr : ∀ᵐ a ∂μ.restrict s, Q a * R a = R a * Q a :=
      (ae_restrict_iff_subtype (μ := μ)
        (p := fun a => Q a * R a = R a * Q a) hs).mpr hcommOn
    have hs' : ∀ᵐ a ∂μ, a ∈ s := mem_ae_iff.mpr hnull
    filter_upwards [hs', ae_imp_of_ae_restrict hr] with a ha h
    exact h ha
  exact (boundedFieldOperator_commutes_of_ae μ Q hmeas C hbound T R hR hcomm).symm

/-- A bounded measurable central selector on the genuine conull fibers
reconstructs a central operator in the represented von Neumann algebra. -/
theorem boundedFieldOperator_central_of_restricted_fibers
    (s : Set Ω) (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (σ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (ρ : ∀ _a : s, A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b : A, ∀ f : Lp H 2 μ,
      ∀ᵐ a : s ∂Measure.comap ((↑) : s → Ω) μ, σ b f a = ρ a b (f a))
    (hlocal : ∀ (t : Set Ω) (ht : MeasurableSet t),
      l2Localization μ t ht ∈ representationVonNeumannAlgebra σ)
    (Q : Ω → H →L[ℂ] H)
    (hmeas : ∀ x : H, AEStronglyMeasurable (fun a => Q a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖Q a‖ ≤ C)
    (hmem : ∀ᵐ a : s ∂Measure.comap ((↑) : s → Ω) μ,
      Q a ∈ representationVonNeumannAlgebra (ρ a))
    (hcentral : ∀ᵐ a : s ∂Measure.comap ((↑) : s → Ω) μ,
      Q a ∈ (representationVonNeumannAlgebra (ρ a)).commutant) :
    boundedFieldOperator μ Q hmeas C hbound ∈ representationVonNeumannAlgebra σ ∧
      boundedFieldOperator μ Q hmeas C hbound ∈
        (representationVonNeumannAlgebra σ).commutant := by
  refine ⟨boundedFieldOperator_mem_of_restricted_fiber_bicommutants
    μ s hs hnull σ ρ hσ hlocal Q hmeas C hbound hmem, ?_⟩
  apply (mem_representation_commutant_iff σ _).mpr
  rintro _ ⟨b, rfl⟩
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hleft := (ae_restrict_iff_subtype hs).mp
    (ae_restrict_of_ae (boundedFieldOperator_action μ Q hmeas C hbound f))
  have hright := (ae_restrict_iff_subtype hs).mp (ae_restrict_of_ae
    (boundedFieldOperator_action μ Q hmeas C hbound (σ b f)))
  have hOn : ∀ᵐ a : s ∂Measure.comap ((↑) : s → Ω) μ,
      (σ b * boundedFieldOperator μ Q hmeas C hbound) f a =
        (boundedFieldOperator μ Q hmeas C hbound * σ b) f a := by
    filter_upwards [hσ b (boundedFieldOperator μ Q hmeas C hbound f), hσ b f,
      hleft, hright, hcentral] with a hσleft hσright hqleft hqright hc
    change σ b (boundedFieldOperator μ Q hmeas C hbound f) a =
      boundedFieldOperator μ Q hmeas C hbound (σ b f) a
    rw [hσleft, hqleft, hqright, hσright]
    exact congrArg (fun U : H →L[ℂ] H => U (f a))
      (VonNeumannAlgebra.mem_commutant_iff.mp hc _
        (mem_representationVonNeumannAlgebra (ρ a) b))
  have hr : ∀ᵐ a ∂μ.restrict s,
      (σ b * boundedFieldOperator μ Q hmeas C hbound) f a =
        (boundedFieldOperator μ Q hmeas C hbound * σ b) f a :=
    (ae_restrict_iff_subtype (μ := μ) (p := fun a =>
      (σ b * boundedFieldOperator μ Q hmeas C hbound) f a =
        (boundedFieldOperator μ Q hmeas C hbound * σ b) f a) hs).mpr hOn
  have hs' : ∀ᵐ a ∂μ, a ∈ s := mem_ae_iff.mpr hnull
  filter_upwards [hs', ae_imp_of_ae_restrict hr] with a ha h
  exact h ha

end KadisonSimilarity

end

end OAI
