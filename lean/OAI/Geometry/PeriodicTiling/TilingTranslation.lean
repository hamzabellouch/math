import OAI.Geometry.PeriodicTiling.TilingBasic
import Mathlib.Tactic.Abel

namespace OAI

universe uG

namespace PeriodicTilingThree

variable {G : Type uG} [AddCommGroup G] [DecidableEq G]

theorem Tiles.translate_tile {F : Finset G} {A : Set G}
    (h : Tiles F A) (v : G) : Tiles (F.image (fun f => f + v)) A := by
  classical
  apply tiles_iff_unique_tile.mpr
  intro x
  obtain ⟨f, hf, huniq⟩ := tiles_iff_unique_tile.mp h (x - v)
  refine ⟨⟨(f : G) + v, Finset.mem_image.mpr ⟨f, f.property, rfl⟩⟩, ?_, ?_⟩
  · change x - ((f : G) + v) ∈ A
    have heq : x - ((f : G) + v) = x - v - (f : G) := by abel
    rw [heq]
    exact hf
  · intro g hg
    obtain ⟨f', hf', hfg⟩ := Finset.mem_image.mp g.property
    have heq : x - (f' + v) = x - v - f' := by abel
    change x - (g : G) ∈ A at hg
    rw [← hfg, heq] at hg
    have hff : (⟨f', hf'⟩ : ↥F) = f := huniq _ hg
    apply Subtype.ext
    change (g : G) = (f : G) + v
    rw [← hfg]
    exact congrArg (fun z : G => z + v) (congrArg Subtype.val hff)

theorem tiles_translate_tile_iff (F : Finset G) (A : Set G) (v : G) :
    Tiles (F.image (fun f => f + v)) A ↔ Tiles F A := by
  constructor
  · intro h
    have h' := h.translate_tile (-v)
    simpa only [Finset.image_image, Function.comp_def, add_neg_cancel_right, Finset.image_id'] using h'
  · intro h
    exact h.translate_tile v

theorem exists_zero_mem_normalization (F : Finset G) (hF : F.Nonempty)
    (htile : ∃ A, Tiles F A)
    (haperiodic : ∀ A, Tiles F A → ¬ FullyPeriodic A) :
    ∃ U : Finset G, 0 ∈ U ∧
      (∃ A, Tiles U A) ∧ (∀ A, Tiles U A → ¬ FullyPeriodic A) := by
  classical
  obtain ⟨f0, hf0⟩ := hF
  refine ⟨F.image (fun f => f + -f0), ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨f0, hf0, add_neg_cancel f0⟩
  · obtain ⟨A, hA⟩ := htile
    exact ⟨A, hA.translate_tile (-f0)⟩
  · intro A hA
    exact haperiodic A ((tiles_translate_tile_iff F A (-f0)).mp hA)

end PeriodicTilingThree

end OAI
