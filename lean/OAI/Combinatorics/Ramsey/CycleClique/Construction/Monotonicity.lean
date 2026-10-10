import OAI.Combinatorics.Ramsey.CycleClique.Construction.Definitions

namespace OAI

namespace CycleClique.Construction
/-- Enlarging the vertex set preserves the forcing property. -/
theorem RamseyProperty.mono {m n M N : ℕ} (h : RamseyProperty m n M) (hMN : M ≤ N) :
    RamseyProperty m n N := by
  intro G
  let f : Fin M → Fin N := Fin.castLE hMN
  have hf : Function.Injective f := Fin.castLE_injective hMN
  rcases h (G.comap f) with hc | hi
  · exact Or.inl (hc.map f hf (fun h => h))
  · exact Or.inr (hi.map f hf (fun h => h))

/-- A coloring avoiding the two targets restricts to every smaller order. -/
theorem not_ramseyProperty_mono {m n M N : ℕ}
    (h : ¬ RamseyProperty m n N) (hMN : M ≤ N) : ¬ RamseyProperty m n M :=
  fun hM => h (hM.mono hMN)

/-- A forcing upper bound and a coloring one vertex below it determine the number. -/
theorem isRamseyNumber_of_upper_lower {m n N : ℕ}
    (hupper : RamseyProperty m n (N + 1)) (hlower : ¬ RamseyProperty m n N) :
    IsRamseyNumber m n (N + 1) := by
  refine ⟨hupper, fun M hM => not_ramseyProperty_mono hlower ?_⟩
  omega

end CycleClique.Construction

end OAI
