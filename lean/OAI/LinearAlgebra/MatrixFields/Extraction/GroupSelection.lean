import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.GroupDegreeEnvelope
import OAI.LinearAlgebra.MatrixFields.Construction.GroupNativeDegreeBound

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupSelection

open MatrixMultiplication.Foundation AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldScheduledYield AllFieldNativeCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

def orbitPrefactor (allocation : Allocation) (sigma : Placement) : ℕ :=
  3 * (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick)
    allocation + 1) ^ AllFieldGroupOrbitCount.groupDegree K tick sigma

theorem data_orbits_card_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement)
    (e : AllFieldGroupOrbitData.Targets (K := K) (tick := tick) allocation m sigma) :
    ((AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m ε sigma).orbits e).card ≤
      orbitPrefactor (K := K) (tick := tick) allocation sigma *
        (m + 1) ^ AllFieldGroupOrbitCount.groupDegree K tick sigma := by
  have hb := AllFieldGroupOrbitData.orbits_card_le allocation m ε sigma e
  unfold orbitPrefactor AllFieldGroupOrbitCount.groupOrbitPrefactor at *
  exact_mod_cast hb

theorem data_coarse_injective (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) :
    Function.Injective
      (AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m ε sigma).coarse :=
  AllFieldGroupOrbitData.coarse_injective allocation m sigma

structure Selected (allocation : Allocation) (m : ℕ) (width : ℝ)
    (sigma : Placement) (slack : ℝ) where
  sample : JointCoarseHashing.Sample
    (AllFieldGroupOrbitData.Pos (K := K) (tick := tick) allocation m sigma)
    (JointOrdinarySelection.hashLevel
      (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
  targets : Finset (AllFieldGroupOrbitData.Targets
    (K := K) (tick := tick) allocation m sigma)
  card_targets : targets.card =
    ⌊Real.exp ((m : ℝ) * (nativeCapacity (K := K) (tick := tick) allocation - slack))⌋₊
  good : ∀ e ∈ targets,
    (AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m width sigma).Good
      (JointOrdinarySelection.hashLevel
        (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
      (JointOrdinarySelection.hashSet
        (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
      (m : ℝ) e sample
  distinct_first : ∀ e ∈ targets, ∀ f ∈ targets, e ≠ f →
    (AllFieldGroupOrbitData.coarse (K := K) (tick := tick) allocation m sigma e).1 ≠
      (AllFieldGroupOrbitData.coarse (K := K) (tick := tick) allocation m sigma f).1

end MatrixMultiplication.AllFieldGroupSelection

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
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
      (K := K) (tick := tick) allocation sigma
      (show 0 < slack / 4 by linarith) hwidthMax
  refine ⟨threshold, hthreshold, hthresholdMax, ?_⟩
  intro width hwidth hsmall
  apply selected_of_native_count_bound (K := K) (tick := tick) allocation sigma width hslack
  simpa only [nativeDegree, AllFieldGroupNativeDegreeBound.maxNativeDegree] using
    hcounts width hwidth hsmall

end MatrixMultiplication.AllFieldGroupSelection

end
end

end MatrixAllFields

end OAI
