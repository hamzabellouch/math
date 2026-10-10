import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityModel

namespace OAI

/-! High ordinary density supplies concrete tests and then a finite
popular forest. Every tile receives a keeper whose direction belongs to
the tile's original dyadic interval. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem densitySpatialBox_mono (T : SlopeBox) {K K' : ℝ} (h : K ≤ K') :
    densitySpatialBox T K ⊆ densitySpatialBox T K' := by
  intro z hz
  exact ⟨hz.1.trans (mul_le_mul_of_nonneg_right h T.length_pos.le),
    hz.2.trans (mul_le_mul_of_nonneg_right h T.width_pos.le)⟩

theorem exists_high_density_forest (a : ℝ) (ha : 0 ≤ a) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (ι : Type*) (tiles : Finset ι) (tile : ι → OrdinaryDensityTile)
      (ell0 w W tau : ℝ) (q : ℤ), 0 < ell0 → 0 < w → 12*w ≤ W →
    ∀ (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ), MeasurableSet E →
      (volume.prod volume) E ≠ ∞ → Measurable u →
      (∀ i ∈ tiles, L^(-a) < (tile i).density ell0 w W tau q E u) →
    ∃ (test : ∀ i : tiles, OrdinaryDensityTest ell0 w W tau q (tile i))
      (keepers : Finset tiles) (assigned : tiles → keepers),
      let witness := fun i : tiles => densityTest E u (test i).top
        (scaledAngularCell (w/ell0) q (test i).level (test i).cell) (L^(a/100+1))
      (∀ i ∈ keepers, MeasurableSet (witness i)) ∧
      Set.PairwiseDisjoint (keepers : Set tiles) witness ∧
      (∑ i ∈ keepers, (test i).top.area) ≤ 2*L^a*(volume.prod volume).real E ∧
      (∀ i ∈ keepers, L^(-(a+2))*(test i).top.area ≤ (volume.prod volume).real (witness i)) ∧
      (∀ i ∈ keepers, ∀ z ∈ witness i, z ∈ E ∧ (test i).top.radius z ≤ L^(a+2) ∧
        |u z-(test i).top.slope| ≤ w/(test i).top.length ∧
        |u z-(test i).top.slope| ≤ (test i).top.width/(12*(test i).top.length)) ∧
      (∀ i : tiles,
        ell0/DyadicLineGrid.scale (tile i).level ≤ (test (assigned i).val).top.length ∧
        (test (assigned i).val).top.radius (tile i).center ≤ L^(a+2) ∧
        (test (assigned i).val).top.slope ∈
          scaledAngularCell (w/ell0) q (tile i).level (tile i).cell) := by
  classical
  obtain ⟨L0,hL0,hforest⟩ := exists_power_density_forest a ha
  refine ⟨L0,hL0,?_⟩
  intro L hL ι tiles tile ell0 w W tau q hell0 hw hW E u hE hEfin hu hdensity
  have hLp : 0 < L := by linarith [hL0.trans hL]
  have hL1 : 1 ≤ L := by linarith [hL0.trans hL]
  have htest (i : tiles) : ∃ test : OrdinaryDensityTest ell0 w W tau q (tile i),
      L^(-a)*test.top.area < ∫ z in E ∩
        u ⁻¹' scaledAngularCell (w/ell0) q test.level test.cell,
        test.top.densityKernel 203 z ∂volume.prod volume :=
    (tile i).exists_test_of_lt_density ell0 w W tau q E u (Real.rpow_nonneg hLp.le _)
      (hdensity i i.property)
  let test := fun i : tiles => Classical.choose (htest i)
  have hchosen (i : tiles) := Classical.choose_spec (htest i)
  obtain ⟨keepers,hsub,hmeas,hdisj,harea,hsize,hinside,hcover⟩ := hforest L hL tiles
    Finset.univ (fun i => (test i).top) (fun i => (test i).level) (fun i => (test i).cell)
    q ell0 w W hell0 hw hW (fun i _ => (test i).length_eq) (fun i _ => (test i).width_eq)
    (fun i _ => (test i).slope_mem_self) E u hE hEfin hu (fun i _ => (hchosen i).le)
  let assigned : tiles → keepers := fun i =>
    ⟨Classical.choose (hcover i (Finset.mem_univ i)),
      (Classical.choose_spec (hcover i (Finset.mem_univ i))).1⟩
  refine ⟨test,keepers,assigned,hmeas,hdisj,harea,hsize,hinside,?_⟩
  intro i
  have hassigned := (Classical.choose_spec (hcover i (Finset.mem_univ i))).2
  change (test i).top.length ≤ (test (assigned i).val).top.length ∧
      scaledAngularCell (w/ell0) q (test (assigned i).val).level (test (assigned i).val).cell ⊆
        scaledAngularCell (w/ell0) q (test i).level (test i).cell ∧
      ∀ z ∈ densitySpatialBox (test i).top (L^(a/100+1)),
        (test (assigned i).val).top.radius z ≤ L^(a+2) at hassigned
  have hK : (1/2:ℝ) ≤ L^(a/100+1) :=
    (by norm_num : (1/2:ℝ) ≤ 1).trans (Real.one_le_rpow hL1 (by linarith))
  have hcenter := densitySpatialBox_mono (test i).top hK (test i).center_mem
  have hlevels : (test i).level ≤ (tile i).level := density_dyadic_length_order hell0
    (by simpa only [(test i).length_eq] using (test i).tile_length_le)
  have hnested : scaledAngularCell (w/ell0) q (test i).level (test i).cell ⊆
      scaledAngularCell (w/ell0) q (tile i).level (tile i).cell :=
    scaledAngularCell_subset hlevels
      ⟨(test i).top.slope,(test i).slope_mem_tile,(test i).slope_mem_self⟩
  exact ⟨(test i).tile_length_le.trans hassigned.1,hassigned.2.2 _ hcenter,
    hnested (hassigned.2.1 (test (assigned i).val).slope_mem_self)⟩

end LipschitzHilbert

end

end OAI
