import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityPowerForest

namespace OAI

/-! The ordinary density is the supremum of the manuscript's actual
weighted box tests. Exceeding a threshold supplies a concrete test, which
can then be fed to the finite keeper construction. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

structure OrdinaryDensityTile where
  center : ℝ×ℝ
  level : ℤ
  cell : ℤ

structure OrdinaryDensityTest (ell0 w W tau : ℝ) (q : ℤ) (tile : OrdinaryDensityTile) where
  top : SlopeBox
  level : ℤ
  cell : ℤ
  length_eq : top.length = ell0/DyadicLineGrid.scale level
  width_eq : top.width = W
  length_le : top.length ≤ tau
  tile_length_le : ell0/DyadicLineGrid.scale tile.level ≤ top.length
  center_mem : tile.center ∈ densitySpatialBox top (1/2)
  slope_mem_tile : top.slope ∈ scaledAngularCell (w/ell0) q tile.level tile.cell
  slope_mem_self : top.slope ∈ scaledAngularCell (w/ell0) q level cell

def densityAverage (T : SlopeBox) (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (omega : Set ℝ) : ℝ :=
  (∫ z in E ∩ u ⁻¹' omega, T.densityKernel 203 z ∂volume.prod volume)/T.area

theorem densityAverage_nonneg (T : SlopeBox) (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ)
    (omega : Set ℝ) : 0 ≤ densityAverage T E u omega := by
  apply div_nonneg _ T.area_pos.le
  exact integral_nonneg (fun z => T.densityKernel_nonneg 203 z)

theorem densityAverage_le (T : SlopeBox) (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ)
    (omega : Set ℝ) : densityAverage T E u omega ≤ ∫ z, topProfile 203 z ∂volume.prod volume := by
  unfold densityAverage
  apply (div_le_iff₀ T.area_pos).mpr
  have h := setIntegral_le_integral (s := E ∩ u ⁻¹' omega)
    (T.densityKernel_integrable (by norm_num : (2:ℝ)<203))
    (Filter.Eventually.of_forall (fun z => T.densityKernel_nonneg 203 z))
  exact h.trans_eq (T.integral_densityKernel 203)

namespace OrdinaryDensityTile

def densityValues (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) : Set ℝ :=
  insert 0 (Set.range fun test : OrdinaryDensityTest ell0 w W tau q tile =>
    densityAverage test.top E u (scaledAngularCell (w/ell0) q test.level test.cell))

def density (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) : ℝ :=
  sSup (tile.densityValues ell0 w W tau q E u)

theorem densityValues_nonempty (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    (tile.densityValues ell0 w W tau q E u).Nonempty := ⟨0,Or.inl rfl⟩

theorem densityValues_bddAbove (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    BddAbove (tile.densityValues ell0 w W tau q E u) := by
  refine ⟨∫ z, topProfile 203 z ∂volume.prod volume,?_⟩
  intro x hx
  rcases hx with rfl | ⟨test,rfl⟩
  · exact integral_nonneg (topProfile_nonnegative 203)
  · exact densityAverage_le test.top E u _

theorem density_nonneg (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) : 0 ≤ tile.density ell0 w W tau q E u :=
  le_csSup (tile.densityValues_bddAbove ell0 w W tau q E u) (Or.inl rfl)

theorem density_le (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    tile.density ell0 w W tau q E u ≤ ∫ z, topProfile 203 z ∂volume.prod volume := by
  apply csSup_le (tile.densityValues_nonempty ell0 w W tau q E u)
  intro x hx
  rcases hx with rfl | ⟨test,rfl⟩
  · exact integral_nonneg (topProfile_nonnegative 203)
  · exact densityAverage_le test.top E u _

theorem exists_test_of_lt_density (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) {eta : ℝ} (heta : 0 ≤ eta)
    (h : eta < tile.density ell0 w W tau q E u) :
    ∃ test : OrdinaryDensityTest ell0 w W tau q tile,
      eta*test.top.area < ∫ z in E ∩
        u ⁻¹' scaledAngularCell (w/ell0) q test.level test.cell,
        test.top.densityKernel 203 z ∂volume.prod volume := by
  obtain ⟨x,hx,hlt⟩ := (lt_csSup_iff
    (tile.densityValues_bddAbove ell0 w W tau q E u)
    (tile.densityValues_nonempty ell0 w W tau q E u)).mp h
  rcases hx with rfl | ⟨test,rfl⟩
  · exact (not_lt_of_ge heta hlt).elim
  · exact ⟨test,(lt_div_iff₀ test.top.area_pos).mp hlt⟩

theorem density_mono (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    {E F : Set (ℝ×ℝ)} (hEF : E ⊆ F) (u : ℝ×ℝ → ℝ) :
    tile.density ell0 w W tau q E u ≤ tile.density ell0 w W tau q F u := by
  apply csSup_le (tile.densityValues_nonempty ell0 w W tau q E u)
  intro x hx
  rcases hx with rfl | ⟨test,rfl⟩
  · exact tile.density_nonneg ell0 w W tau q F u
  · have hmono : densityAverage test.top E u (scaledAngularCell (w/ell0) q test.level test.cell) ≤
        densityAverage test.top F u (scaledAngularCell (w/ell0) q test.level test.cell) := by
      apply div_le_div_of_nonneg_right _ test.top.area_pos.le
      apply setIntegral_mono_set
        (test.top.densityKernel_integrable (by norm_num : (2:ℝ)<203)).integrableOn
        (Filter.Eventually.of_forall (fun z => test.top.densityKernel_nonneg 203 z))
      exact Filter.Eventually.of_forall (fun z hz => ⟨hEF hz.1,hz.2⟩)
    apply hmono.trans
    exact le_csSup (tile.densityValues_bddAbove ell0 w W tau q F u) (Or.inr ⟨test,rfl⟩)

end OrdinaryDensityTile
end LipschitzHilbert

end

end OAI
