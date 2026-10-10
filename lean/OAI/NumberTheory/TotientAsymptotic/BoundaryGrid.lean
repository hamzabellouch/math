import OAI.NumberTheory.TotientAsymptotic.BoundaryAggregation
import OAI.NumberTheory.TotientAsymptotic.VolumeComparison

namespace OAI

/-! The actual finite boundary-box error in the prime mass comparison. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def witnessBandedRegion (x : ℝ) (H : ℕ) (η : TailDatum H) : Set (Fin (R x H) → ℝ) :=
  perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H

def witnessBoundaryGrid (x : ℝ) (H : ℕ) (η : TailDatum H) : Finset (Fin (R x H) → ℕ) :=
  gridOuter (bandGrid x H) (witnessBandedRegion x H η) \
    gridInner (bandGrid x H) (witnessBandedRegion x H η)

lemma gridBoundary_card_eq {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ)) :
    ((gridOuter K S).card : ℝ)-(gridInner K S).card =
      ((gridOuter K S \ gridInner K S).card : ℝ) := by
  rw [Finset.card_sdiff_of_subset (gridInner_subset_outer K S),
    Nat.cast_sub (Finset.card_le_card (gridInner_subset_outer K S))]

lemma gridBoundary_card_bound {x : ℝ} {H : ℕ}
    (hs : theta x ∈ Set.Ico (0 : ℝ) 1) (d : ℕ) :
    ((gridOuter (bandGrid x H) (bandedWitnessRegion x H d)).card : ℝ)-
      (gridInner (bandGrid x H) (bandedWitnessRegion x H d)).card ≤
    ∑ η ∈ witnessFinset H (theta x) d, ((witnessBoundaryGrid x H η).card : ℝ) := by
  rw [gridBoundary_card_eq]
  have hcover : gridOuter (bandGrid x H) (bandedWitnessRegion x H d) \
      gridInner (bandGrid x H) (bandedWitnessRegion x H d) ⊆
      (witnessFinset H (theta x) d).biUnion (witnessBoundaryGrid x H) := by
    intro b hb
    obtain ⟨ho, hn⟩ := Finset.mem_sdiff.mp hb
    obtain ⟨hbK, u, hub, hu⟩ := Finset.mem_filter.mp ho
    rw [bandedWitnessRegion_eq hs] at hu
    obtain ⟨η, hη⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hη, huη⟩ := Set.mem_iUnion.mp hη
    apply Finset.mem_biUnion.mpr
    refine ⟨η, hη, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨hbK, u, hub, huη⟩
    · intro hinner
      have hall := (Finset.mem_filter.mp hinner).2
      apply hn
      refine Finset.mem_filter.mpr ⟨hbK, ?_⟩
      intro v hv
      rw [bandedWitnessRegion_eq hs]
      exact Set.mem_iUnion.mpr ⟨η, Set.mem_iUnion.mpr ⟨hη, hall hv⟩⟩
  exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le

lemma witnessBoundaryGrid_crossing {x : ℝ} {H : ℕ} {η : TailDatum H}
    {u : Fin (R x H) → ℝ} (hu : u ∈ gridRegion (witnessBoundaryGrid x H η)) :
    ∃ u₀ ∈ witnessBandedRegion x H η, (∀ i, |u₀ i-u i| ≤ 1) ∧
      ∃ w, w ∉ witnessBandedRegion x H η ∧ ∀ i, |w i-u i| ≤ 1 := by
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hu
  obtain ⟨hb, hub⟩ := Set.mem_iUnion.mp hb
  obtain ⟨hbout, hbin⟩ := Finset.mem_sdiff.mp hb
  obtain ⟨hbK, u₀, h₀b, h₀⟩ := Finset.mem_filter.mp hbout
  have hnot : ¬ unitGridCell b ⊆ witnessBandedRegion x H η := by
    intro hsub
    exact hbin (Finset.mem_filter.mpr ⟨hbK, hsub⟩)
  obtain ⟨w₀, hwb, hw₀⟩ := Set.not_subset.mp hnot
  exact ⟨u₀, h₀, unitGridCell_coordinate_distance h₀b hub,
    w₀, hw₀, unitGridCell_coordinate_distance hwb hub⟩

/-- The boundary-cardinality term appearing in the actual prime-grid
sandwich has a vanishing normalized reciprocal-tail-weighted sum. -/
theorem weighted_boundary_grid_error (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput)
    (hford : FordCoordinateConcentrationInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ Finset.Icc 1 (tailValueBound H), (d : ℝ)⁻¹*
        (((gridOuter (bandGrid x H) (bandedWitnessRegion x H d)).card : ℝ)-
          (gridInner (bandGrid x H) (bandedWitnessRegion x H d)).card))/G x (m x) ≤ ε H := by
  obtain ⟨ε, hε, hbound⟩ := witness_boundary_aggregation hbox hmertens hren hford
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hbound] with H hH
  filter_upwards [hH, theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hs hB
  have hh := hx (activeWitnesses H (theta x))
    (fun η hη => (mem_activeWitnesses hs).mp hη)
    (fun η => gridRegion (witnessBoundaryGrid x H η))
    (fun η _ => (witnessBoundaryGrid x H η).measurableSet_biUnion
      (fun b _ => measurableSet_unitGridCell b))
    (fun η _ _ hu => witnessBoundaryGrid_crossing hu)
  apply le_trans _ hh
  apply div_le_div_of_nonneg_right _ (G_pos hB _).le
  simp_rw [show ∀ η : TailDatum H, volume.real (gridRegion (witnessBoundaryGrid x H η)) =
      ((witnessBoundaryGrid x H η).card : ℝ) by intro η; exact gridRegion_volume_real _]
  rw [← weighted_witness_fibers hs]
  exact Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left (gridBoundary_card_bound hs d) (by positivity))

end TotientAsymptotic

end

end OAI
