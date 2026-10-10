import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.SelectionCore
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.MaskedGoodSelection
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.DegreeEnvelope
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.NativeDegreeBound

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupSelection

open MatrixMultiplication.Foundation AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldScheduledYield AllFieldNativeCapacity
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

private theorem selected_of_native_count_bound
    (allocation : Allocation) (sigma : Placement) (width : ℝ)
    {slack : ℝ} (hslack : 0 < slack)
    (hcounts : ∀ᶠ m : ℕ in atTop,
      (∀ e : AllFieldGroupOrbitData.Targets (K := K) (tick := tick) allocation m sigma,
        (((AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤
          Real.exp ((m : ℝ) *
            (nativeDegree (K := K) (tick := tick) allocation sigma + slack / 4))) ∧
      (∀ e : AllFieldGroupOrbitData.Targets (K := K) (tick := tick) allocation m sigma,
        ∀ o ∈ (AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m width sigma).orbits e,
          ∀ v ∈ (AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m width sigma).passing e o,
            (((AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card : ℝ) ≤
              Real.exp ((m : ℝ) *
                (nativeDegree (K := K) (tick := tick) allocation sigma + slack / 4)))) :
    ∀ᶠ m : ℕ in atTop,
      Nonempty (Selected (K := K) (tick := tick) allocation m width sigma slack) := by
  have hD : 0 ≤ nativeDegree (K := K) (tick := tick) allocation sigma + slack / 4 := by
    linarith [nativeDegree_nonneg (K := K) (tick := tick) allocation sigma]
  have hdegree := AllFieldGroupDegreeEnvelope.eventually_log_uniformDegree_le
    allocation width sigma hD hcounts
  have hrate : ∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop,
      Real.log (AllFieldGroupDegreeEnvelope.uniformDegree
        (K := K) (tick := tick) allocation m width sigma : ℝ) / (m : ℝ) ≤
          nativeDegree (K := K) (tick := tick) allocation sigma + slack / 4 + η := by
    intro η hη
    filter_upwards [hdegree] with m hm
    linarith
  let : ∀ m : ℕ, Fintype (AllFieldGroupOrbitData.Pos
      (K := K) (tick := tick) allocation m sigma) := fun m => inferInstance
  let : ∀ m : ℕ, Fintype (AllFieldGroupOrbitData.Targets
      (K := K) (tick := tick) allocation m sigma) := fun m => inferInstance
  have hselected := JointMaskedGoodSelection.eventually_exists_good_selection
    (fun m => AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m width sigma)
    (fun m => data_coarse_injective (K := K) (tick := tick) allocation m width sigma)
    (fun m => AllFieldGroupDegreeEnvelope.uniformDegree (K := K) (tick := tick) allocation m width sigma)
    (orbitPrefactor (K := K) (tick := tick) allocation sigma)
    (AllFieldGroupOrbitCount.groupDegree K tick sigma)
    (fun m => AllFieldGroupDegreeEnvelope.eligibility_card_le (K := K) (tick := tick) allocation m width sigma)
    (fun m => AllFieldGroupDegreeEnvelope.competitors_card_le (K := K) (tick := tick) allocation m width sigma)
    (fun m => data_orbits_card_le (K := K) (tick := tick) allocation m width sigma)
    (selectionHashRate_nonneg (K := K) (tick := tick) allocation sigma hslack)
    (selectionHashRate_window_gap (K := K) (tick := tick) allocation sigma hslack) hrate
    (Eventually.of_forall (AllFieldGroupTargetRate.target_card_pos
      (K := K) (tick := tick) (sigma := sigma) allocation))
    (AllFieldGroupTargetRate.tendsto_log_target_card_div
      (K := K) (tick := tick) (sigma := sigma) allocation)
    (half_pos hslack)
  filter_upwards [hselected] with m hm
  obtain ⟨s, G, hcard, hgood, hdistinct⟩ := hm
  refine ⟨{
    sample := s
    targets := G
    card_targets := ?_
    good := hgood
    distinct_first := hdistinct }⟩
  simpa only [selection_exponent] using hcard

theorem exists_threshold_eventually_selected
    (allocation : Allocation) (sigma : Placement)
    {slack widthMax : ℝ} (hslack : 0 < slack) (hwidthMax : 0 < widthMax) :
    ∃ threshold : ℝ, 0 < threshold ∧ threshold ≤ widthMax ∧
      ∀ width : ℝ, 0 < width → width ≤ threshold →
        ∀ᶠ m : ℕ in atTop,
          Nonempty (Selected (K := K) (tick := tick) allocation m width sigma slack) := by
  obtain ⟨threshold, hthreshold, hthresholdMax, hcounts⟩ :=
    AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le
      (K := K) (tick := tick) (δ := slack / 4) allocation sigma
      (div_pos hslack (by norm_num)) hwidthMax
  refine ⟨threshold, hthreshold, hthresholdMax, ?_⟩
  intro width hwidth hsmall
  apply selected_of_native_count_bound (K := K) (tick := tick) allocation sigma width hslack
  simpa only [nativeDegree, AllFieldGroupNativeDegreeBound.maxNativeDegree] using
    hcounts width hwidth hsmall

end MatrixMultiplication.AllFieldGroupSelection

end

end OAI
