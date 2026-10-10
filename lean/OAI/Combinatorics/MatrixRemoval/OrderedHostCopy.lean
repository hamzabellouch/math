import OAI.Combinatorics.MatrixRemoval.OrderedBodyLocalization
import OAI.Combinatorics.MatrixRemoval.PinnedHostCopy

namespace OAI

/-!
# Ordered-copy localization and counting

The six-mode body theorem places the distinguished cell at a shared leaf.
The count needs only anchor pinning, not a further order certificate.
-/

namespace Problem348.OrderedHost

open Construction

/-- The six-mode theorem supplies the exact body-localization counting input. -/
theorem orderedBodyLocalizes (h : ℕ) :
    OrderedBodyLocalizes (rowIndex h) (columnIndex h) := by
  intro t r₀ r₁ c₀ c₁ hr₀ hr₁ hc₀ hc₁ hrow hcol hb
  exact body_leaf_diagonal hr₀ hr₁ hc₀ hc₁ hrow hcol hb

/-- Every matching ordered copy has its top-left body cell at a shared leaf. -/
theorem matching_copy_leaf_of_pinning (h : ℕ)
    (hpin : Anchor64Pinned (rowIndex h) (columnIndex h))
    (r c : Fin 66 → Position h)
    (hr : StrictMono (fun i => rowIndex h (r i)))
    (hc : StrictMono (fun j => columnIndex h (c j)))
    (hmatch : ∀ i j, host (r i) (c j) = fixedH i j) :
    ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z :=
  host_raw_localization_of_anchor_pinning (rowIndex h) (columnIndex h)
    hpin (orderedBodyLocalizes h) r c hr hc hmatch

/-- Integer copy bound for the actual two-axis enumeration. -/
theorem copyCount_le_of_pinning (h : ℕ)
    (hpin : Anchor64Pinned (rowIndex h) (columnIndex h)) :
    copyCount fixedH (hostMatrix (rowIndex h) (columnIndex h)) ≤
      2 ^ h * (size h) ^ 130 :=
  host_copyCount_le_of_pinning (rowIndex h) (columnIndex h)
    hpin (orderedBodyLocalizes h)

/-- The normalized copy bound, conditional only on anchor pinning. -/
theorem copyDensity_le_of_pinning (h : ℕ)
    (hpin : Anchor64Pinned (rowIndex h) (columnIndex h)) :
    (copyCount fixedH (hostMatrix (rowIndex h) (columnIndex h)) : ℝ) /
        ((size h : ℝ) ^ 132) ≤
      (1 / (((386 * h + 2 : ℕ) : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) :=
  host_copyDensity_le_of_pinning h (rowIndex h) (columnIndex h)
    hpin (orderedBodyLocalizes h)

end Problem348.OrderedHost

end OAI
