import Mathlib.Data.Finset.Filter
import Mathlib.Data.Set.Image

namespace OAI

/-! # Finite tile covers retaining the actual good-probe witnesses -/

namespace PolycyclicRecognition

/-- Image collisions need not have a preferred inverse. A finite image
set is covered by the images of its good-probe tiles, with a witness in
the original retained set for every tile membership. -/
theorem exists_probe_image_tile_cover {Y G : Type*} {m : ℕ}
    (K : Set Y) (image : Y → G) (tile : Y → Fin m) (source : Finset G)
    (hsource : (source : Set G) ⊆ image '' K) :
    ∃ points : Fin m → Finset G,
      (∀ j, points j ⊆ source) ∧
      (∀ x ∈ source, ∃ j, x ∈ points j) ∧
      ∀ j x, x ∈ points j ↔ x ∈ source ∧ ∃ y ∈ K, tile y = j ∧ image y = x := by
  classical
  let points := fun j => source.filter (fun x => ∃ y ∈ K, tile y = j ∧ image y = x)
  refine ⟨points, fun _ => Finset.filter_subset _ _, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, he⟩ := hsource hx
    exact ⟨tile y, Finset.mem_filter.mpr ⟨hx, y, hy, rfl, he⟩⟩
  · intro j x
    exact Finset.mem_filter

/-- The same construction simultaneously chooses the finite tile cover
at every scale of the probe sequence. -/
theorem exists_probe_image_tile_cover_sequence {Y : ℕ → Type*} {G : Type*}
    (K : ∀ n, Set (Y n)) (image : ∀ n, Y n → G) (tiles : ℕ → ℕ)
    (tile : ∀ n, Y n → Fin (tiles n)) (source : ℕ → Finset G)
    (hsource : ∀ n, (source n : Set G) ⊆ image n '' K n) :
    ∃ points : ∀ n, Fin (tiles n) → Finset G,
      (∀ n j, points n j ⊆ source n) ∧
      (∀ n x, x ∈ source n → ∃ j, x ∈ points n j) ∧
      ∀ n j x, x ∈ points n j ↔
        x ∈ source n ∧ ∃ y ∈ K n, tile n y = j ∧ image n y = x := by
  classical
  choose points hsub hcover hpoint using fun n =>
    exists_probe_image_tile_cover (K n) (image n) (tile n) (source n) (hsource n)
  exact ⟨points, hsub, hcover, hpoint⟩

end PolycyclicRecognition

end OAI
