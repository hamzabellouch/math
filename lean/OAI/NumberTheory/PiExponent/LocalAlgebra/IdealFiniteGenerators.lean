import Mathlib

namespace OAI

namespace PiExponent.IdealFiniteGenerators

theorem exists_generators {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : ∃ m : ℕ, ∃ a : Fin m → I,
      Ideal.span (Set.range fun j => (a j).val) = I := by
  obtain ⟨m,b,hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  let a : Fin m → I := fun j => ⟨b j, by
    rw [← hb]
    exact Submodule.subset_span ⟨j,rfl⟩⟩
  exact ⟨m,a,hb⟩

end PiExponent.IdealFiniteGenerators

end OAI
