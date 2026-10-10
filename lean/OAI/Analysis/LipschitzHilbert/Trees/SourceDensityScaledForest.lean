import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityForest

namespace OAI

/-! The angular grid has physical scale w/topLength. Keeping that scale
explicit allows arbitrary vertical band width and dyadic source lengths. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

def scaledAngularCell (unit : ℝ) (q k j : ℤ) : Set ℝ :=
  {s | s/unit ∈ DyadicLineGrid.cell q k j}

theorem scaledAngularCell_measurable (unit : ℝ) (q k j : ℤ) :
    MeasurableSet (scaledAngularCell unit q k j) :=
  measurableSet_Ico.preimage (measurable_id.div_const unit)

theorem scaledAngularCell_nonempty {unit : ℝ} (hunit : 0 < unit) (q k j : ℤ) :
    (scaledAngularCell unit q k j).Nonempty := by
  obtain ⟨s,hs⟩ := DyadicLineGrid.cell_nonempty q k j
  refine ⟨s*unit,?_⟩
  simpa only [scaledAngularCell,mem_ofPred_eq,mul_div_cancel_right₀ _ hunit.ne'] using hs

theorem scaledAngularCell_subset {unit : ℝ} {q k l i j : ℤ} (hlk : l ≤ k)
    (hinter : (scaledAngularCell unit q k i ∩ scaledAngularCell unit q l j).Nonempty) :
    scaledAngularCell unit q l j ⊆ scaledAngularCell unit q k i := by
  obtain ⟨s,hs,ht⟩ := hinter
  have hnested := DyadicLineGrid.cell_subset_of_intersect hlk ⟨s/unit,ht,hs⟩
  intro t ht
  exact hnested ht

theorem scaledAngularCell_slope {unit : ℝ} (hunit : 0 < unit) {q k l i j : ℤ} {s t : ℝ}
    (hlk : l ≤ k)
    (hinter : (scaledAngularCell unit q k i ∩ scaledAngularCell unit q l j).Nonempty)
    (hs : s ∈ scaledAngularCell unit q k i) (ht : t ∈ scaledAngularCell unit q l j) :
    |s-t| ≤ unit*DyadicLineGrid.scale k := by
  obtain ⟨v,hv,hv'⟩ := hinter
  have h := density_angular_cell_slope hlk ⟨v/unit,hv,hv'⟩ hs ht
  rw [←sub_div,abs_div,abs_of_pos hunit] at h
  simpa only [mul_comm] using (div_le_iff₀ hunit).mp h

theorem exists_scaled_dyadic_density_forest {ι : Type*} (candidates : Finset ι)
    (T : ι → SlopeBox) (level cell : ι → ℤ) (q : ℤ) (unit K C eta : ℝ)
    (hunit : 0 < unit) (hK : 0 ≤ K) (hC : 0 ≤ C) (heta : 0 < eta)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (hE : MeasurableSet E)
    (hEfinite : (volume.prod volume) E ≠ ∞) (hu : Measurable u)
    (horder : ∀ i ∈ candidates, ∀ j ∈ candidates,
      (T i).length ≤ (T j).length → level j ≤ level i)
    (hwidth : ∀ i ∈ candidates, ∀ j ∈ candidates, (T i).width = (T j).width)
    (hslope : ∀ i ∈ candidates,
      (T i).slope ∈ scaledAngularCell unit q (level i) (cell i))
    (hangular : ∀ i ∈ candidates,
      (unit*DyadicLineGrid.scale (level i))*(T i).length ≤ C*(T i).width)
    (hmass : ∀ i ∈ candidates, eta*(T i).area ≤
      (volume.prod volume).real
        (densityTest E u (T i) (scaledAngularCell unit q (level i) (cell i)) K)) :
    ∃ keepers : Finset ι, keepers ⊆ candidates ∧
      (∀ i ∈ keepers, MeasurableSet
        (densityTest E u (T i) (scaledAngularCell unit q (level i) (cell i)) K)) ∧
      Set.PairwiseDisjoint (keepers : Set ι)
        (fun i => densityTest E u (T i) (scaledAngularCell unit q (level i) (cell i)) K) ∧
      (∑ i ∈ keepers, (T i).area) ≤ (volume.prod volume).real E/eta ∧
      (∀ i ∈ keepers, ∀ z ∈ densityTest E u (T i)
          (scaledAngularCell unit q (level i) (cell i)) K,
        z ∈ E ∧ |u z-(T i).slope| ≤ unit*DyadicLineGrid.scale (level i)) ∧
      (∀ i ∈ candidates, ∃ j ∈ keepers,
        (T i).length ≤ (T j).length ∧
        scaledAngularCell unit q (level j) (cell j) ⊆
          scaledAngularCell unit q (level i) (cell i) ∧
        densitySpatialBox (T i) K ⊆ densitySpatialBox (T j) ((3+2*C)*K)) := by
  let omega := fun i => scaledAngularCell unit q (level i) (cell i)
  obtain ⟨keepers,hsub,hdisj,hcover⟩ := exists_density_keepers candidates T omega K hK
    (fun i _ => scaledAngularCell_nonempty hunit q (level i) (cell i))
  have hm (i : ι) : MeasurableSet (densityTest E u (T i) (omega i) K) :=
    densityTest_measurable hE hu (scaledAngularCell_measurable unit q (level i) (cell i)) (T i) K
  refine ⟨keepers,hsub,fun i _ => hm i,?_,?_,?_,?_⟩
  · intro i hi j hj hij
    exact densityTest_disjoint_of_not_conflict E u T omega K (hdisj i hi j hj hij)
  · exact density_keeper_area_budget keepers T omega K eta E u heta hEfinite hdisj
      (fun i _ => hm i) (fun i hi => hmass i (hsub hi))
  · intro i hi z hz
    refine ⟨hz.1.1,?_⟩
    exact scaledAngularCell_slope hunit (le_refl (level i))
      ⟨(T i).slope,hslope i (hsub hi),hslope i (hsub hi)⟩ hz.2 (hslope i (hsub hi))
  · intro i hi
    obtain ⟨j,hj,hlen,hconflict⟩ := hcover i hi
    have hjc := hsub hj
    have hlevels := horder i hi j hjc hlen
    have hnested : omega j ⊆ omega i := scaledAngularCell_subset hlevels hconflict.2
    have hs : |(T i).slope-(T j).slope| * (T i).length ≤ C*(T j).width := by
      calc
        _ ≤ (unit*DyadicLineGrid.scale (level i))*(T i).length :=
          mul_le_mul_of_nonneg_right
            (scaledAngularCell_slope hunit hlevels hconflict.2 (hslope i hi) (hslope j hjc))
            (T i).length_pos.le
        _ ≤ C*(T i).width := hangular i hi
        _ = _ := by rw [hwidth i hi j hjc]
    exact ⟨j,hj,hlen,hnested,density_box_subset_keeper (T i) (T j) hK hC hlen
      (hwidth i hi j hjc) hs hconflict.1⟩

end LipschitzHilbert

end

end OAI
