import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularGridRebase
import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityModel

namespace OAI

/-! The weighted density tests are invariant under a dyadic change of
starting scale. Their physical boxes and integrals are unchanged. -/
noncomputable section
open Set
namespace LipschitzHilbert
open DyadicLineGrid

def OrdinaryDensityTile.rebase (tile : OrdinaryDensityTile) (h : ℤ) : OrdinaryDensityTile :=
  { tile with level := tile.level-h }

theorem density_rebase_length (ell0 : ℝ) (h k : ℤ) :
    (ell0/scale h)/scale (k-h)=ell0/scale k := by
  simp only [scale,zpow_sub₀ (by norm_num : (2:ℝ)≠0)]
  field_simp

theorem density_rebase_cell (ell0 w : ℝ) (hell0 : 0<ell0) (hw : 0<w)
    (q h k j : ℤ) :
    scaledAngularCell (w/(ell0/scale h)) ((h.negOnePow : ℤ)*q) (k-h) j=
      scaledAngularCell (w/ell0) q k j := by
  have he : w/(ell0/scale h)=(w/ell0)*scale h := by field_simp
  rw [he,scaledAngularCell_rebase _ (div_pos hw hell0)]
  congr 1
  omega

def OrdinaryDensityTest.rebase {ell0 w W tau : ℝ} {q : ℤ} {tile : OrdinaryDensityTile}
    (test : OrdinaryDensityTest ell0 w W tau q tile)
    (h : ℤ) (hell0 : 0<ell0) (hw : 0<w) :
    OrdinaryDensityTest (ell0/scale h) w W tau ((h.negOnePow : ℤ)*q) (tile.rebase h) where
  top := test.top
  level := test.level-h
  cell := test.cell
  length_eq := test.length_eq.trans (density_rebase_length ell0 h test.level).symm
  width_eq := test.width_eq
  length_le := test.length_le
  tile_length_le := by
    simpa only [OrdinaryDensityTile.rebase,density_rebase_length] using test.tile_length_le
  center_mem := test.center_mem
  slope_mem_tile := by
    simpa only [OrdinaryDensityTile.rebase,density_rebase_cell ell0 w hell0 hw] using test.slope_mem_tile
  slope_mem_self := by
    simpa only [density_rebase_cell ell0 w hell0 hw] using test.slope_mem_self

/-- Each original test has exactly the same weighted average after rebasing. -/
theorem density_rebase_test_value {ell0 w W tau : ℝ} {q : ℤ} {tile : OrdinaryDensityTile}
    (test : OrdinaryDensityTest ell0 w W tau q tile)
    (h : ℤ) (hell0 : 0<ell0) (hw : 0<w)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    densityAverage (test.rebase h hell0 hw).top E u
      (scaledAngularCell (w/(ell0/scale h)) ((h.negOnePow : ℤ)*q)
        (test.rebase h hell0 hw).level (test.rebase h hell0 hw).cell)=
    densityAverage test.top E u (scaledAngularCell (w/ell0) q test.level test.cell) := by
  simp only [OrdinaryDensityTest.rebase,density_rebase_cell ell0 w hell0 hw]

def OrdinaryDensityTest.restore {ell0 w W tau : ℝ} {q : ℤ} {tile : OrdinaryDensityTile}
    (h : ℤ) (hell0 : 0<ell0) (hw : 0<w)
    (test : OrdinaryDensityTest (ell0/scale h) w W tau ((h.negOnePow : ℤ)*q) (tile.rebase h)) :
    OrdinaryDensityTest ell0 w W tau q tile where
  top := test.top
  level := test.level+h
  cell := test.cell
  length_eq := by
    rw [test.length_eq,←density_rebase_length ell0 h (test.level+h)]
    simp only [add_sub_cancel_right]
  width_eq := test.width_eq
  length_le := test.length_le
  tile_length_le := by
    simpa only [OrdinaryDensityTile.rebase,density_rebase_length] using test.tile_length_le
  center_mem := test.center_mem
  slope_mem_tile := by
    simpa only [OrdinaryDensityTile.rebase,density_rebase_cell ell0 w hell0 hw] using test.slope_mem_tile
  slope_mem_self := by
    have he := density_rebase_cell ell0 w hell0 hw q h (test.level+h) test.cell
    rw [add_sub_cancel_right] at he
    rw [←he]
    exact test.slope_mem_self

theorem density_restore_test_value {ell0 w W tau : ℝ} {q : ℤ} {tile : OrdinaryDensityTile}
    (h : ℤ) (hell0 : 0<ell0) (hw : 0<w)
    (test : OrdinaryDensityTest (ell0/scale h) w W tau ((h.negOnePow : ℤ)*q) (tile.rebase h))
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    densityAverage (test.restore h hell0 hw).top E u
      (scaledAngularCell (w/ell0) q (test.restore h hell0 hw).level (test.restore h hell0 hw).cell)=
    densityAverage test.top E u (scaledAngularCell (w/(ell0/scale h))
      ((h.negOnePow : ℤ)*q) test.level test.cell) := by
  have he := density_rebase_cell ell0 w hell0 hw q h (test.level+h) test.cell
  rw [add_sub_cancel_right] at he
  simp only [OrdinaryDensityTest.restore,←he]

/-- All weighted box tests, including tests above the initial scale,
correspond in both directions, hence the density is exactly preserved. -/
theorem OrdinaryDensityTile.density_rebase (tile : OrdinaryDensityTile)
    (ell0 w W tau : ℝ) (h : ℤ) (q : ℤ) (hell0 : 0<ell0) (hw : 0<w)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    (tile.rebase h).density (ell0/scale h) w W tau ((h.negOnePow : ℤ)*q) E u=
      tile.density ell0 w W tau q E u := by
  unfold OrdinaryDensityTile.density
  congr 1
  ext x
  constructor
  · intro hx
    rcases hx with rfl | ⟨test,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨test.restore h hell0 hw,density_restore_test_value h hell0 hw test E u⟩
  · intro hx
    rcases hx with rfl | ⟨test,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨test.rebase h hell0 hw,density_rebase_test_value test h hell0 hw E u⟩

end LipschitzHilbert

end

end OAI
