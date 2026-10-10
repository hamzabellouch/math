import OAI.Geometry.PeriodicTiling.TilingBasic

namespace OAI

universe uG

namespace PeriodicTilingThree

section Region

variable {G : Type uG} [AddCommGroup G]

structure TilesRegion (F : Finset G) (D E : Set G) : Prop where
  add_mem : ∀ f ∈ F, ∀ d ∈ D, f + d ∈ E
  unique : ∀ x ∈ E, ∃! f : ↥F, x - (f : G) ∈ D

theorem tilesRegion_univ_iff {F : Finset G} {D : Set G} :
    TilesRegion F D Set.univ ↔ Tiles F D := by
  rw [tiles_iff_unique_tile]
  constructor
  · intro h x
    exact h.unique x (Set.mem_univ x)
  · intro h
    exact ⟨fun _ _ _ _ => Set.mem_univ _, fun x _ => h x⟩

theorem TilesRegion.mem_iff {F : Finset G} {D E : Set G}
    (h : TilesRegion F D E) (x : G) :
    x ∈ E ↔ ∃ f : ↥F, x - (f : G) ∈ D := by
  constructor
  · intro hx
    obtain ⟨f, hf, _⟩ := h.unique x hx
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    simpa [add_comm] using h.add_mem f f.property (x - f) hf

theorem TilesRegion.of_local_copy {F : Finset G} {D D' E : Set G}
    (h : TilesRegion F D E)
    (hcopy : ∀ x : G, ∃ y : G, (y ∈ E ↔ x ∈ E) ∧
      ∀ f : ↥F, (x - (f : G) ∈ D' ↔ y - (f : G) ∈ D)) :
    TilesRegion F D' E := by
  constructor
  · intro f hf d hd
    obtain ⟨y, hE, htests⟩ := hcopy (f + d)
    apply hE.mp
    apply (h.mem_iff y).mpr
    refine ⟨⟨f, hf⟩, (htests ⟨f, hf⟩).mp ?_⟩
    simpa using hd
  · intro x hx
    obtain ⟨y, hE, htests⟩ := hcopy x
    obtain ⟨f, hf, huniq⟩ := h.unique y (hE.mpr hx)
    refine ⟨f, (htests f).mpr hf, ?_⟩
    intro g hg
    exact huniq g ((htests g).mp hg)

end Region

end PeriodicTilingThree

end OAI
