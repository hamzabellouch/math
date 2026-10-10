import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalOnlineKeys
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalProgramEquality

namespace OAI

/-! The local online provider reads a scale/center key directly; the
complete representative index identifies the corresponding action. -/

namespace EditApproximation

theorem localOnlineCandidates_integer_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (tau a eta kappa : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (left right : ℕ → TargetInterval target.length → ℕ) (q : TargetInterval target.length)
    (hequal : ∀ b ∈ dyadicQueryWindow N (parentInitial q) a F,
      (b, roundInterval (seedGridSpacing b P) q) ∈ representativeList N P F a parentInitial →
      left b (roundInterval (seedGridSpacing b P) q) = right b (roundInterval (seedGridSpacing b P) q)) :
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t left q =
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t right q := by
  unfold localOnlineCandidates
  apply List.filterMap_congr
  intro b hb
  dsimp only
  split_ifs with heligible
  · have hrep := representativeList_mem a parentInitial _ (List.mem_filter.mp hb).1
      (roundInterval_on_grid _ q) heligible.1 heligible.2
    rw [hequal b hb hrep]
  · rfl

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H : ℕ) (tau eta kappa : ℚ)
  (draw : PhysicalLocalOnlineDraw source target U N P F A R T exponent H tau)

def physicalRawOnlineIntegers (node : PhysicalInternalNode M J) (time : Fin R)
    (b : ℕ) (r : TargetInterval target.length) : ℕ :=
  if hb : b ∈ dyadicScales N then
    (draw (node, physicalScaleIndex N b hb, r) time).val
  else 0

variable (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)

def physicalOnlineStreamsOfRaw :
    PhysicalOnlineStreams source target U N P F A T exponent H tau R :=
  fun node representative time =>
    Fin.cast (physicalLocalOnlineMass_on_key source target U N P F A T exponent H tau
      hsize hP hF hA hseed ⟨node, representative⟩)
      (draw (physicalOnlineRawKey source target U N P F A ⟨node, representative⟩) time)

omit [NeZero R] in
theorem physicalRawOnlineIntegers_get (node : PhysicalInternalNode M J)
    (representative : Fin (stageRepresentatives source target U N P F A node.1).length)
    (time : Fin R) :
    physicalRawOnlineIntegers source target U N P F A T exponent H tau draw node time
        ((stageRepresentatives source target U N P F A node.1).get representative).1
        ((stageRepresentatives source target U N P F A node.1).get representative).2 =
      (physicalOnlineStreamsOfRaw source target U N P F A T exponent H tau draw
        hsize hP hF hA hseed node representative time).val := by
  unfold physicalRawOnlineIntegers physicalOnlineStreamsOfRaw
  rw [dite_eq_left (representativeList_scale_mem _ _ (List.get_mem _ representative))]
  exact (Fin.val_cast
    (physicalLocalOnlineMass_on_key source target U N P F A T exponent H tau
      hsize hP hF hA hseed ⟨node, representative⟩)
    (draw (physicalOnlineRawKey source target U N P F A ⟨node, representative⟩) time)).symm

theorem physicalRawOnline_eq_adapter :
    physicalLocalOnline source target U N P F exponent H T A tau eta kappa
      (physicalRawOnlineIntegers source target U N P F A T exponent H tau draw) =
    physicalLocalOnline source target U N P F exponent H T A tau eta kappa
      (physicalOnlineIntegersOfStreams source target U N P F exponent H T A tau
        (physicalOnlineStreamsOfRaw source target U N P F A T exponent H tau draw
          hsize hP hF hA hseed)) := by
  funext node children t q
  unfold physicalLocalOnline
  split_ifs with hbelow
  · apply localOnlineCandidates_integer_congr
    intro b _hb hrep
    obtain ⟨representative, hget⟩ := List.mem_iff_get.mp hrep
    change (stageRepresentatives source target U N P F A node).get representative =
      (b, roundInterval (seedGridSpacing b P) q) at hget
    have hraw := physicalRawOnlineIntegers_get source target U N P F A T exponent H tau draw
      hsize hP hF hA hseed ⟨node, hbelow⟩ representative (Fin.ofNat R (t - 1))
    have hold := physicalOnlineIntegersOfStreams_get source target U N P F exponent H T A tau
      (physicalOnlineStreamsOfRaw source target U N P F A T exponent H tau draw
        hsize hP hF hA hseed) ⟨node, hbelow⟩ representative (Fin.ofNat R (t - 1))
    rw [hget] at hraw hold
    exact hraw.trans hold.symm
  · rfl

theorem physicalRawOnlineProgram_eq (Q : ℕ) (delta : ℚ)
    (groups : PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    physicalLocalRefinement source target U N P F exponent Q A tau delta T
      (fun label s => groups label (Fin.ofNat R (s - 1)))
      (physicalLocalOnline source target U N P F exponent H T A tau eta kappa
        (physicalRawOnlineIntegers source target U N P F A T exponent H tau draw)) node t q =
    physicalRefinement source target U N P F A T delta
      (physicalProgramSelections source target U N P F A T exponent H Q tau eta kappa
        (physicalOnlineStreamsOfRaw source target U N P F A T exponent H tau draw
          hsize hP hF hA hseed)
        (physicalGroupStreamsOfKeys source target U N P F exponent Q A groups)) node t q := by
  rw [physicalRawOnline_eq_adapter source target U N P F A T exponent H tau eta kappa draw
    hsize hP hF hA hseed]
  exact physicalLocalProgram_eq source target U N P F exponent Q H T A tau delta eta kappa
    _ groups hsize hP hF hA hseed node t q

end Program

end EditApproximation

end OAI
