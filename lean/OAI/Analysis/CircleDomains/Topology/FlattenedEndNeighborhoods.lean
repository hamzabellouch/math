import OAI.Analysis.CircleDomains.Sobolev.ScalarFlattening

namespace OAI

/-! Finitely many flattened coordinates have a common constancy
neighborhood at each specified end value. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem flattened_coordinates_constant_near
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (f : ι → X → ℝ) {p : X} (hf : ∀ i, ContinuousAt (f i) p)
    (O : ι → Set ℝ) (hO : ∀ i, IsOpen (O i)) (hp : ∀ i, f i p ∈ O i) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧
      ∀ i, EqOn (fun x => flattenValues (O i) (f i x))
        (fun _ => flattenValues (O i) (f i p)) V := by
  have hi (i : ι) : ∀ᶠ x in 𝓝 p,
      flattenValues (O i) (f i x) = flattenValues (O i) (f i p) := by
    obtain ⟨W, hW, hconst⟩ := flattenValues_locally_constant (hO i) (hp i)
    exact ((hf i).eventually hW).mono (fun x hx => hconst hx)
  have hall : ∀ᶠ x in 𝓝 p, ∀ i,
      flattenValues (O i) (f i x) = flattenValues (O i) (f i p) :=
    Filter.eventually_all.mpr hi
  obtain ⟨V, hsub, hV, hpV⟩ := mem_nhds_iff.mp hall
  exact ⟨V, hV, hpV, fun i x hx => hsub hx i⟩

end CircleDomainRigidity

end

end OAI
