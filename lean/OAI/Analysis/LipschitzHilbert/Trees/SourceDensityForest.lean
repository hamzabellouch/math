import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityGeometry

namespace OAI

/-! Density witnesses generate an actual finite keeper forest. The
disjointness, area budget, angular nesting and enlarged spatial assignment
are conclusions of the selection, not assumptions on the forest. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem exists_dyadic_density_forest {ι : Type*} (candidates : Finset ι)
    (T : ι → SlopeBox) (level cell : ι → ℤ) (q : ℤ) (K C eta : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (heta : 0 < eta)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (hE : MeasurableSet E)
    (hEfinite : (volume.prod volume) E ≠ ∞) (hu : Measurable u)
    (horder : ∀ i ∈ candidates, ∀ j ∈ candidates,
      (T i).length ≤ (T j).length → level j ≤ level i)
    (hwidth : ∀ i ∈ candidates, ∀ j ∈ candidates, (T i).width = (T j).width)
    (hslope : ∀ i ∈ candidates,
      (T i).slope ∈ DyadicLineGrid.cell q (level i) (cell i))
    (hangular : ∀ i ∈ candidates,
      DyadicLineGrid.scale (level i)*(T i).length ≤ C*(T i).width)
    (hmass : ∀ i ∈ candidates, eta*(T i).area ≤
      (volume.prod volume).real
        (densityTest E u (T i) (DyadicLineGrid.cell q (level i) (cell i)) K)) :
    ∃ keepers : Finset ι, keepers ⊆ candidates ∧
      (∀ i ∈ keepers, MeasurableSet
        (densityTest E u (T i) (DyadicLineGrid.cell q (level i) (cell i)) K)) ∧
      Set.PairwiseDisjoint (keepers : Set ι)
        (fun i => densityTest E u (T i) (DyadicLineGrid.cell q (level i) (cell i)) K) ∧
      (∑ i ∈ keepers, (T i).area) ≤ (volume.prod volume).real E/eta ∧
      (∀ i ∈ keepers, ∀ z ∈ densityTest E u (T i)
          (DyadicLineGrid.cell q (level i) (cell i)) K,
        z ∈ E ∧ |u z-(T i).slope| ≤ DyadicLineGrid.scale (level i)) ∧
      (∀ i ∈ candidates, ∃ j ∈ keepers,
        (T i).length ≤ (T j).length ∧
        DyadicLineGrid.cell q (level j) (cell j) ⊆
          DyadicLineGrid.cell q (level i) (cell i) ∧
        densitySpatialBox (T i) K ⊆ densitySpatialBox (T j) ((3+2*C)*K)) := by
  let omega := fun i => DyadicLineGrid.cell q (level i) (cell i)
  obtain ⟨keepers,hsub,hdisj,hcover⟩ := exists_density_keepers candidates T omega K hK
    (fun i _ => DyadicLineGrid.cell_nonempty q (level i) (cell i))
  have hm (i : ι) : MeasurableSet (densityTest E u (T i) (omega i) K) :=
    densityTest_measurable hE hu measurableSet_Ico (T i) K
  refine ⟨keepers,hsub,fun i _ => hm i,?_,?_,?_,?_⟩
  · intro i hi j hj hij
    exact densityTest_disjoint_of_not_conflict E u T omega K (hdisj i hi j hj hij)
  · exact density_keeper_area_budget keepers T omega K eta E u heta hEfinite hdisj
      (fun i _ => hm i) (fun i hi => hmass i (hsub hi))
  · intro i hi z hz
    refine ⟨hz.1.1,?_⟩
    exact density_angular_cell_slope (le_refl (level i))
      ⟨(T i).slope,hslope i (hsub hi),hslope i (hsub hi)⟩ hz.2 (hslope i (hsub hi))
  · intro i hi
    obtain ⟨j,hj,hlen,hconflict⟩ := hcover i hi
    have hjc := hsub hj
    have hlevels := horder i hi j hjc hlen
    have hnested : omega j ⊆ omega i := DyadicLineGrid.cell_subset_of_intersect hlevels
      (by simpa only [inter_comm] using hconflict.2)
    have hs : |(T i).slope-(T j).slope| * (T i).length ≤ C*(T j).width := by
      calc
        _ ≤ DyadicLineGrid.scale (level i)*(T i).length :=
          mul_le_mul_of_nonneg_right
            (density_angular_cell_slope hlevels hconflict.2 (hslope i hi) (hslope j hjc))
            (T i).length_pos.le
        _ ≤ C*(T i).width := hangular i hi
        _ = _ := by rw [hwidth i hi j hjc]
    exact ⟨j,hj,hlen,hnested,density_box_subset_keeper (T i) (T j) hK hC hlen
      (hwidth i hi j hjc) hs hconflict.1⟩

end LipschitzHilbert

end

end OAI
