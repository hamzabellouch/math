import OAI.Geometry.PeriodicTiling.TilingBasic

namespace OAI

universe uG uH

namespace PeriodicTilingThree

section

variable {G : Type uG} {H : Type uH} [AddCommGroup G] [AddCommGroup H] [DecidableEq H]

theorem tiles_preimage_of_section (φ : G →+ H)
    {U : Finset G} {F : Finset H} {A : Set H}
    (himage : U.image φ = F) (hinj : Set.InjOn φ (U : Set G))
    (h : Tiles F A) : Tiles U (φ ⁻¹' A) := by
  classical
  apply tiles_iff_unique_tile.mpr
  intro g
  obtain ⟨f, hf, huniq⟩ := tiles_iff_unique_tile.mp h (φ g)
  have hfimage : (f : H) ∈ U.image φ := by
    rw [himage]
    exact f.property
  obtain ⟨u, hu, huf⟩ := Finset.mem_image.mp hfimage
  refine ⟨⟨u, hu⟩, ?_, ?_⟩
  · change φ (g - u) ∈ A
    simpa only [map_sub, huf] using hf
  · intro v hv
    have hvF : φ (v : G) ∈ F := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨v, v.property, rfl⟩
    have hvA : φ g - φ (v : G) ∈ A := by
      simpa only [Set.mem_preimage, map_sub] using hv
    have hvf : (⟨φ (v : G), hvF⟩ : ↥F) = f := huniq _ hvA
    apply Subtype.ext
    apply hinj v.property hu
    exact (congrArg Subtype.val hvf).trans huf.symm

theorem tiles_image_of_kernel_periods (φ : G →+ H)
    (hφ : Function.Surjective φ) {U : Finset G} {B : Set G}
    (h : Tiles U B) (hker : ∀ k ∈ φ.ker, Period B k) :
    Tiles (U.image φ) (φ '' B) := by
  classical
  apply tiles_iff_unique_tile.mpr
  intro y
  obtain ⟨g, hg⟩ := hφ y
  obtain ⟨u, hu, huniq⟩ := tiles_iff_unique_tile.mp h g
  have hfu : φ (u : G) ∈ U.image φ :=
    Finset.mem_image.mpr ⟨u, u.property, rfl⟩
  refine ⟨⟨φ (u : G), hfu⟩, ?_, ?_⟩
  · refine ⟨g - (u : G), hu, ?_⟩
    simp only [map_sub, hg]
  · intro f hf
    obtain ⟨v, hv, hvf⟩ := Finset.mem_image.mp f.property
    obtain ⟨b, hb, hbf⟩ := hf
    have hgvb : φ (g - v - b) = 0 := by
      simp only [map_sub, hg, hvf, hbf, sub_self]
    have hk : g - v - b ∈ φ.ker := hgvb
    have hgv : g - v ∈ B := by
      have hp := (hker (g - v - b) hk b).mpr hb
      have heq : b + (g - v - b) = g - v := by
        rw [add_comm, sub_add_cancel]
      rw [heq] at hp
      exact hp
    have hvu : (⟨v, hv⟩ : ↥U) = u := huniq _ hgv
    apply Subtype.ext
    calc
      (f : H) = φ v := hvf.symm
      _ = φ (u : G) := congrArg φ (congrArg Subtype.val hvu)

end

end PeriodicTilingThree

end OAI
