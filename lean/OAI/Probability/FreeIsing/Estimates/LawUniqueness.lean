import Mathlib

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem measure_eq_of_cofinal_restrict_eq
    {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    {μ ν : Measure (∀ i, α i)} [IsFiniteMeasure μ]
    (C : Finset ι → Prop)
    (hC : ∀ D : Finset ι, ∃ E, D ⊆ E ∧ C E)
    (h : ∀ E : Finset ι, C E → μ.map E.restrict = ν.map E.restrict) :
    μ = ν := by
  apply IsProjectiveLimit.unique (P := fun D : Finset ι => μ.map D.restrict)
  · intro D
    rfl
  · intro D
    obtain ⟨E, hDE, hE⟩ := hC D
    have heq := congrArg (fun ρ => ρ.map (Finset.restrict₂ hDE)) (h E hE)
    rw [Measure.map_map (Finset.measurable_restrict₂ hDE) (Finset.measurable_restrict E),
      Measure.map_map (Finset.measurable_restrict₂ hDE) (Finset.measurable_restrict E)] at heq
    exact heq.symm

theorem map_restrict_eq_of_cylinder_eq
    {ι α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Finite α] [Nonempty α]
    (μ ν : Measure (ι → α)) (D : Finset ι)
    (h : ∀ η : ι → α,
      μ {x | ∀ v ∈ D, x v = η v} = ν {x | ∀ v ∈ D, x v = η v}) :
    μ.map D.restrict = ν.map D.restrict := by
  classical
  apply Measure.ext_of_singleton
  intro η
  let η' : ι → α := fun v => if hv : v ∈ D then η ⟨v, hv⟩ else Classical.choice inferInstance
  have hset : (D.restrict : (ι → α) → (D → α)) ⁻¹' {η} = {x | ∀ v ∈ D, x v = η' v} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro hx v hv
      have hv' := congrFun hx ⟨v, hv⟩
      simpa [η', hv, Finset.restrict_def] using hv'
    · intro hx
      funext v
      simpa [η', v.property, Finset.restrict_def] using hx v v.property
  rw [Measure.map_apply (Finset.measurable_restrict D) (measurableSet_singleton η),
    Measure.map_apply (Finset.measurable_restrict D) (measurableSet_singleton η), hset]
  exact h η'

theorem measure_eq_of_cofinal_cylinders
    {ι α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Finite α] [Nonempty α]
    {μ ν : Measure (ι → α)} [IsFiniteMeasure μ]
    (C : Finset ι → Prop)
    (hC : ∀ D : Finset ι, ∃ E, D ⊆ E ∧ C E)
    (h : ∀ E : Finset ι, C E → ∀ η : ι → α,
      μ {x | ∀ v ∈ E, x v = η v} = ν {x | ∀ v ∈ E, x v = η v}) :
    μ = ν := by
  apply measure_eq_of_cofinal_restrict_eq C hC
  intro E hE
  exact map_restrict_eq_of_cylinder_eq μ ν E (h E hE)

end Problem367

end

end OAI
