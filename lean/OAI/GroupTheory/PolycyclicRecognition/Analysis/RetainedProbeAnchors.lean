import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeImageTileCover
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace OAI

/-! # Retaining the good anchors needed by measured packing -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set

/-- Empty image tiles use the original neighboring sheet as anchor.
An occupied tile retains its exact geometric anchor. -/
def occupiedTileAnchor {G X : Type*} {m : ℕ}
    (points : Fin m → Finset X) (anchor : Fin m → G) (fallback : G) (j : Fin m) : G :=
  if (points j).Nonempty then anchor j else fallback

theorem occupiedTileAnchor_eq {G X : Type*} {m : ℕ}
    (points : Fin m → Finset X) (anchor : Fin m → G) (fallback : G)
    {j : Fin m} {x : X} (hx : x ∈ points j) :
    occupiedTileAnchor points anchor fallback j = anchor j := by
  simp [occupiedTileAnchor, show (points j).Nonempty from ⟨x, hx⟩]

/-- The simultaneous good-probe estimate extends to every tile after
replacing empty tiles. This supplies the all-anchor premise of packing
without requiring unselected anchors to have good profiles. -/
theorem occupiedTileAnchor_profile_bound
    {G X W : Type*} [NormedAddCommGroup W]
    {Y : ℕ → Type*} (good : ∀ n, Set (Y n)) (tiles : ℕ → ℕ)
    (tile : ∀ n, Y n → Fin (tiles n))
    (points : ∀ n, Fin (tiles n) → Finset X)
    (anchor : ∀ n, Fin (tiles n) → G) (fallback : ℕ → G)
    (profile : ℕ → G → W) (target : ℕ → W) (ε : ℕ → ℝ)
    (hwitness : ∀ n j x, x ∈ points n j → ∃ y ∈ good n, tile n y = j)
    (hfallback : ∀ᶠ n in atTop, ‖profile n (fallback n) - target n‖ ≤ ε n)
    (hgood : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ‖profile n (anchor n (tile n y)) - target n‖ ≤ ε n) :
    ∀ᶠ n in atTop, ∀ j,
      ‖profile n (occupiedTileAnchor (points n) (anchor n) (fallback n) j) - target n‖ ≤ ε n := by
  filter_upwards [hfallback, hgood] with n hn hgoodn
  intro j
  by_cases h : (points n j).Nonempty
  · obtain ⟨x, hx⟩ := h
    obtain ⟨y, hy, he⟩ := hwitness n j x hx
    rw [occupiedTileAnchor_eq _ _ _ hx, ← he]
    exact hgoodn y hy
  · simpa [occupiedTileAnchor, h] using hn

end PolycyclicRecognition

end

end OAI
