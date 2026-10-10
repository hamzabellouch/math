import OAI.Analysis.LipschitzHilbert.Trees.SourceWhitneyDensityTest

namespace OAI

/-! Original long-packet angular supports lie in the cell of the actual
Whitney density test. This is the common indicator kept on the frozen
main term and the selector error. -/
noncomputable section
open Set
namespace LipschitzHilbert

namespace OrdinaryDensityTest

theorem contains_longer_angular_cell {ell0 w W tau : ℝ} {grid : ℤ}
    {witness : OrdinaryDensityTile} (test : OrdinaryDensityTest ell0 w W tau grid witness)
    (hell0 : 0<ell0) (tile : OrdinaryDensityTile)
    (hlen : test.top.length≤ell0/DyadicLineGrid.scale tile.level)
    (hslope : test.top.slope∈scaledAngularCell (w/ell0) grid tile.level tile.cell) :
    scaledAngularCell (w/ell0) grid tile.level tile.cell ⊆
      scaledAngularCell (w/ell0) grid test.level test.cell := by
  have hlevel : tile.level≤test.level := density_dyadic_length_order hell0
    (by simpa only [test.length_eq] using hlen)
  exact scaledAngularCell_subset hlevel ⟨test.top.slope,test.slope_mem_self,hslope⟩

end OrdinaryDensityTest

/-- Every long original selector vanishes outside the single test cell.
The conclusion applies before any freezing or error decomposition. -/
theorem long_selector_support {ι κ : Type*} {ell0 w W tau : ℝ} {grid : ℤ}
    {witness : OrdinaryDensityTile} (test : OrdinaryDensityTest ell0 w W tau grid witness)
    (hell0 : 0<ell0) (tiles : Finset ι) (tile : ι → OrdinaryDensityTile)
    (selector : ι → κ → ℝ → ℂ)
    (hsupport : ∀ i∈tiles, ∀ a s, selector i a s≠0 →
      s∈scaledAngularCell (w/ell0) grid (tile i).level (tile i).cell)
    (hlen : ∀ i∈tiles, test.top.length≤ell0/DyadicLineGrid.scale (tile i).level)
    (hslope : ∀ i∈tiles, test.top.slope∈scaledAngularCell (w/ell0) grid (tile i).level (tile i).cell)
    {s : ℝ} (hs : s∉scaledAngularCell (w/ell0) grid test.level test.cell) :
    ∀ i∈tiles, ∀ a, selector i a s=0 := by
  intro i hi a
  by_contra hne
  exact hs ((test.contains_longer_angular_cell hell0 (tile i) (hlen i hi) (hslope i hi))
    (hsupport i hi a s hne))

end LipschitzHilbert

end

end OAI
