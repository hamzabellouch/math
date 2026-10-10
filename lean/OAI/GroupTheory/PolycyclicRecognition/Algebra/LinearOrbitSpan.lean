import Mathlib.RepresentationTheory.Irreducible

namespace OAI

/-! # An irreducible linear action spans every nonzero orbit -/

noncomputable section
namespace PolycyclicRecognition

variable {K G V : Type*} [Field K] [Monoid G] [AddCommGroup V] [Module K V]

theorem linear_orbit_span_invariant (ρ : Representation K G V) (v : V) (g : G) :
    ∀ x ∈ Submodule.span K (Set.range (fun h => ρ h v)),
      ρ g x ∈ Submodule.span K (Set.range (fun h => ρ h v)) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    have hm : ρ g (ρ h v) = ρ (g * h) v := by rw [map_mul]; rfl
    rw [hm]
    exact Submodule.subset_span (Set.mem_range_self (g * h))
  | zero => simpa only [map_zero] using (Submodule.zero_mem _)
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

theorem irreducible_linear_orbit_span (ρ : Representation K G V)
    [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) :
    Submodule.span K (Set.range (fun h => ρ h v)) = ⊤ := by
  let W : Subrepresentation ρ :=
    ⟨Submodule.span K (Set.range (fun h => ρ h v)), linear_orbit_span_invariant ρ v⟩
  have hvW : v ∈ W := by
    change v ∈ Submodule.span K (Set.range (fun h => ρ h v))
    have hh : ρ 1 v ∈ Submodule.span K (Set.range (fun h => ρ h v)) :=
      Submodule.subset_span (Set.mem_range_self (1 : G))
    simpa only [map_one, Module.End.one_apply] using hh
  rcases eq_bot_or_eq_top W with hW | hW
  · have : v = 0 := by
      rw [hW] at hvW
      exact hvW
    exact (hv this).elim
  · exact congrArg Subrepresentation.toSubmodule hW

end PolycyclicRecognition

end

end OAI
