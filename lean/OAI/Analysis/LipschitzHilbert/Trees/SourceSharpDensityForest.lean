import OAI.Analysis.LipschitzHilbert.Trees.SourceHighDensityForest

namespace OAI

/-! Ordinary density selection with the actual spatial radius retained.
The area budget costs eta⁻¹; the assigned centers lie in five times the
witness dilation, without the coarser concentration-scale enlargement. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem exists_density_forest_at_radius {ι : Type*} (candidates : Finset ι)
    (T : ι → SlopeBox) (level cell : ι → ℤ) (q : ℤ) (ell0 w W K eta : ℝ)
    (hell0 : 0 < ell0) (hw : 0 < w) (hW : w ≤ W) (hK : 1 ≤ K) (heta : 0 < eta)
    (hlength : ∀ i ∈ candidates, (T i).length = ell0/DyadicLineGrid.scale (level i))
    (hwidth : ∀ i ∈ candidates, (T i).width = W)
    (hslope : ∀ i ∈ candidates,
      (T i).slope ∈ scaledAngularCell (w/ell0) q (level i) (cell i))
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (hE : MeasurableSet E)
    (hEfin : (volume.prod volume) E ≠ ∞) (hu : Measurable u)
    (htail : K^(3-(203:ℝ))*(∫ z, topProfile 3 z ∂volume.prod volume) ≤ eta/2)
    (hdensity : ∀ i ∈ candidates, eta*(T i).area ≤ ∫ z in E ∩
      u ⁻¹' scaledAngularCell (w/ell0) q (level i) (cell i),
      (T i).densityKernel 203 z ∂volume.prod volume) :
    let witness := fun i => densityTest E u (T i)
      (scaledAngularCell (w/ell0) q (level i) (cell i)) K
    ∃ keepers : Finset ι, keepers ⊆ candidates ∧
      (∀ i ∈ keepers, MeasurableSet (witness i)) ∧
      Set.PairwiseDisjoint (keepers : Set ι) witness ∧
      (∑ i ∈ keepers, (T i).area) ≤ 2*(volume.prod volume).real E/eta ∧
      (∀ i ∈ keepers, (eta/2)*(T i).area ≤ (volume.prod volume).real (witness i)) ∧
      (∀ i ∈ keepers, ∀ z ∈ witness i,
        z ∈ E ∧ z ∈ densitySpatialBox (T i) K ∧ |u z-(T i).slope| ≤ w/(T i).length) ∧
      (∀ i ∈ candidates, ∃ j ∈ keepers, (T i).length ≤ (T j).length ∧
        scaledAngularCell (w/ell0) q (level j) (cell j) ⊆
          scaledAngularCell (w/ell0) q (level i) (cell i) ∧
        densitySpatialBox (T i) K ⊆ densitySpatialBox (T j) (5*K)) := by
  intro witness
  have hmass (i : ι) (hi : i ∈ candidates) :
      (eta/2)*(T i).area ≤ (volume.prod volume).real (witness i) :=
    density_witness_mass (T i) hK (by norm_num) heta.le E u
      (scaledAngularCell (w/ell0) q (level i) (cell i)) hE hEfin hu
      (scaledAngularCell_measurable (w/ell0) q (level i) (cell i)) htail (hdensity i hi)
  have horder (i : ι) (hi : i ∈ candidates) (j : ι) (hj : j ∈ candidates)
      (hij : (T i).length ≤ (T j).length) : level j ≤ level i :=
    density_dyadic_length_order hell0 (by simpa only [hlength i hi,hlength j hj] using hij)
  have hang (i : ι) (hi : i ∈ candidates) :
      ((w/ell0)*DyadicLineGrid.scale (level i))*(T i).length ≤ 1*(T i).width := by
    rw [hlength i hi,hwidth i hi,one_mul]
    have heq : ((w/ell0)*DyadicLineGrid.scale (level i))*
        (ell0/DyadicLineGrid.scale (level i)) = w := by
      field_simp [hell0.ne',(DyadicLineGrid.scale_pos (level i)).ne']
    rwa [heq]
  obtain ⟨keepers,hsub,hmeas,hdisj,harea,hinside,hcover⟩ := exists_scaled_dyadic_density_forest
    candidates T level cell q (w/ell0) K 1 (eta/2) (div_pos hw hell0)
    (zero_le_one.trans hK) (by norm_num) (half_pos heta) E u hE hEfin hu horder
    (fun i hi j hj => (hwidth i hi).trans (hwidth j hj).symm) hslope hang hmass
  refine ⟨keepers,hsub,hmeas,hdisj,?_,fun i hi => hmass i (hsub hi),?_,?_⟩
  · exact harea.trans_eq (by ring)
  · intro i hi z hz
    refine ⟨(hinside i hi z hz).1,hz.1.2,?_⟩
    convert (hinside i hi z hz).2 using 1
    rw [hlength i (hsub hi)]
    field_simp [hell0.ne',(DyadicLineGrid.scale_pos (level i)).ne']
  · simpa only [show (3+2*(1:ℝ))=5 by norm_num] using hcover

theorem exists_sharp_high_density_forest {ι : Type*} (tiles : Finset ι)
    (tile : ι → OrdinaryDensityTile) (ell0 w W tau K eta : ℝ) (q : ℤ)
    (hell0 : 0 < ell0) (hw : 0 < w) (hW : w ≤ W) (hK : 1 ≤ K) (heta : 0 < eta)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (hE : MeasurableSet E)
    (hEfin : (volume.prod volume) E ≠ ∞) (hu : Measurable u)
    (htail : K^(3-(203:ℝ))*(∫ z, topProfile 3 z ∂volume.prod volume) ≤ eta/2)
    (hdensity : ∀ i ∈ tiles, eta < (tile i).density ell0 w W tau q E u) :
    ∃ (test : ∀ i : tiles, OrdinaryDensityTest ell0 w W tau q (tile i))
      (keepers : Finset tiles) (assigned : tiles → keepers),
      let witness := fun i : tiles => densityTest E u (test i).top
        (scaledAngularCell (w/ell0) q (test i).level (test i).cell) K
      (∀ i ∈ keepers, MeasurableSet (witness i)) ∧
      Set.PairwiseDisjoint (keepers : Set tiles) witness ∧
      (∑ i ∈ keepers, (test i).top.area) ≤ 2*(volume.prod volume).real E/eta ∧
      (∀ i ∈ keepers, (eta/2)*(test i).top.area ≤ (volume.prod volume).real (witness i)) ∧
      (∀ i ∈ keepers, ∀ z ∈ witness i,
        z ∈ E ∧ z ∈ densitySpatialBox (test i).top K ∧
        |u z-(test i).top.slope| ≤ w/(test i).top.length) ∧
      (∀ i : tiles,
        ell0/DyadicLineGrid.scale (tile i).level ≤ (test (assigned i).val).top.length ∧
        (tile i).center ∈ densitySpatialBox (test (assigned i).val).top (5*K) ∧
        (test (assigned i).val).top.slope ∈
          scaledAngularCell (w/ell0) q (tile i).level (tile i).cell) := by
  classical
  have htest (i : tiles) : ∃ test : OrdinaryDensityTest ell0 w W tau q (tile i),
      eta*test.top.area < ∫ z in E ∩
        u ⁻¹' scaledAngularCell (w/ell0) q test.level test.cell,
        test.top.densityKernel 203 z ∂volume.prod volume :=
    (tile i).exists_test_of_lt_density ell0 w W tau q E u heta.le (hdensity i i.property)
  let test := fun i : tiles => Classical.choose (htest i)
  have hchosen (i : tiles) := Classical.choose_spec (htest i)
  obtain ⟨keepers,hsub,hmeas,hdisj,harea,hmass,hinside,hcover⟩ := exists_density_forest_at_radius
    Finset.univ (fun i => (test i).top) (fun i => (test i).level) (fun i => (test i).cell)
    q ell0 w W K eta hell0 hw hW hK heta (fun i _ => (test i).length_eq)
    (fun i _ => (test i).width_eq) (fun i _ => (test i).slope_mem_self)
    E u hE hEfin hu htail (fun i _ => (hchosen i).le)
  let assigned : tiles → keepers := fun i =>
    ⟨Classical.choose (hcover i (Finset.mem_univ i)),
      (Classical.choose_spec (hcover i (Finset.mem_univ i))).1⟩
  refine ⟨test,keepers,assigned,hmeas,hdisj,harea,hmass,hinside,?_⟩
  intro i
  have hassigned := (Classical.choose_spec (hcover i (Finset.mem_univ i))).2
  change (test i).top.length ≤ (test (assigned i).val).top.length ∧
      scaledAngularCell (w/ell0) q (test (assigned i).val).level (test (assigned i).val).cell ⊆
        scaledAngularCell (w/ell0) q (test i).level (test i).cell ∧
      densitySpatialBox (test i).top K ⊆
        densitySpatialBox (test (assigned i).val).top (5*K) at hassigned
  have hcenter := densitySpatialBox_mono (test i).top
    ((by norm_num : (1/2:ℝ)≤1).trans hK) (test i).center_mem
  have hlevels : (test i).level ≤ (tile i).level := density_dyadic_length_order hell0
    (by simpa only [(test i).length_eq] using (test i).tile_length_le)
  have hnested : scaledAngularCell (w/ell0) q (test i).level (test i).cell ⊆
      scaledAngularCell (w/ell0) q (tile i).level (tile i).cell :=
    scaledAngularCell_subset hlevels
      ⟨(test i).top.slope,(test i).slope_mem_tile,(test i).slope_mem_self⟩
  exact ⟨(test i).tile_length_le.trans hassigned.1,hassigned.2.2 hcenter,
    hnested (hassigned.2.1 (test (assigned i).val).slope_mem_self)⟩

end LipschitzHilbert

end

end OAI
