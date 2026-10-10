import Mathlib

namespace OAI

noncomputable section

namespace Problem346

universe u v

/-- A scalar-valued diagonal-detection principle upgrades to a spanning identity
for the diagonal values of any symmetric multilinear map. -/
theorem span_diagonal_eq_span_range_of_detection
    {V : Type u} {W : Type v} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (n : ℕ)
    (detect : ∀ T : MultilinearMap ℂ (fun _ : Fin n => V) ℂ,
      (∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → V), T (fun i => x (σ i)) = T x) →
      (∀ x : V, T (fun _ => x) = 0) → T = 0)
    (m : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → V),
      m (fun i => x (σ i)) = m x) :
    Submodule.span ℂ (Set.range (fun x : V => m (fun _ => x))) =
      Submodule.span ℂ (Set.range m) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨x, rfl⟩
    exact ⟨fun _ => x, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp
    intro f hf
    have hz : f.compMultilinearMap m = 0 := by
      apply detect
      · intro σ y
        change f (m (fun i => y (σ i))) = f (m y)
        rw [hsym]
      · intro y
        exact (Submodule.mem_dualAnnihilator f).mp hf _
          (Submodule.subset_span ⟨y, rfl⟩)
    exact DFunLike.congr_fun hz x

end Problem346

end

end OAI
