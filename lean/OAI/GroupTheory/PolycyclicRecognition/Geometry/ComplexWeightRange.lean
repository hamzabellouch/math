import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexAdjointGroup

namespace OAI

/-! # Restricting lifted weights to their infinitesimal image -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [IsTopologicalGroup G] [PreconnectedSpace G] {n : ℕ}

/-- Exponential generation ensures the lifted character takes values in
the real linear image of its derivative. -/
theorem exists_range_restricted_complex_weights
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (d : E →ₗ[ℝ] (Fin n → ℂ)) (π : G →* Multiplicative (Fin n → ℂ))
    (hπ : Continuous (fun g => (π g).toAdd))
    (he : ∀ x, (π (Exp x)).toAdd = d x) :
    ∃ q : G →* Multiplicative d.range, Continuous (fun g => (q g).toAdd) ∧
      ∀ x, (q (Exp x)).toAdd = d.rangeRestrict x := by
  let S : Subgroup G :=
    { carrier := {g | (π g).toAdd ∈ d.range}
      one_mem' := by
        change (π 1).toAdd ∈ d.range
        rw [map_one]
        exact d.range.zero_mem
      mul_mem' := by
        intro g h hg hh
        change (π (g * h)).toAdd ∈ d.range
        rw [map_mul]
        exact d.range.add_mem hg hh
      inv_mem' := by
        intro g hg
        change (π g⁻¹).toAdd ∈ d.range
        rw [map_inv]
        exact d.range.neg_mem hg }
  have hex (x : GroupLieAlgebra (𝓘(ℝ, E)) G) : (π (Exp x)).toAdd ∈ d.range := by
    rw [he]
    exact LinearMap.mem_range_self d _
  have hS : S = ⊤ := by
    apply subgroup_eq_top_of_exponential_basis hExp (Module.finBasis ℝ E)
    intro i t
    exact hex _
  have hmem (g : G) : (π g).toAdd ∈ d.range := by
    change g ∈ S
    rw [hS]
    trivial
  let q : G →* Multiplicative d.range :=
    { toFun := fun g => Multiplicative.ofAdd ⟨(π g).toAdd, hmem g⟩
      map_one' := by apply Multiplicative.ext; apply Subtype.ext; exact congrArg Multiplicative.toAdd π.map_one
      map_mul' := by
        intro g h
        apply Multiplicative.ext
        apply Subtype.ext
        exact congrArg Multiplicative.toAdd (π.map_mul g h) }
  refine ⟨q, hπ.subtype_mk hmem, fun x => ?_⟩
  apply Subtype.ext
  exact he x

end PolycyclicRecognition

end

end OAI
