import OAI.Combinatorics.EditApproximation.Geometry.LocalOnlineProgram

namespace OAI

/-! A proof adapter couples the bounded online query loop to the original
finite product slots. The adapter is used only to compare laws: local
execution uses scale/center keys and never searches a complete table. -/

namespace EditApproximation

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent H T : ℕ) (A tau eta kappa : ℚ)
  (online : PhysicalOnlineStreams source target U N P F A T exponent H tau R)

local notation "representatives" => stageRepresentatives source target U N P F A

noncomputable def physicalRepresentativeFin (node : PhysicalNode M J)
    (br : ℕ × TargetInterval target.length) (hbr : br ∈ representatives node) :
    Fin (representatives node).length := Classical.choose (List.mem_iff_get.mp hbr)

theorem physicalRepresentativeFin_get (node : PhysicalNode M J)
    (br : ℕ × TargetInterval target.length) (hbr : br ∈ representatives node) :
    (representatives node).get (physicalRepresentativeFin source target U N P F A node br hbr) = br :=
  Classical.choose_spec (List.mem_iff_get.mp hbr)

noncomputable def physicalOnlineIntegersOfStreams
    (node : PhysicalInternalNode M J) (time : Fin R) (b : ℕ) (r : TargetInterval target.length) : ℕ :=
  if hbr : (b, r) ∈ representatives node.1 then
    (online node (physicalRepresentativeFin source target U N P F A node.1 (b, r) hbr) time).val
  else 0

omit [NeZero R] in
theorem physicalOnlineIntegersOfStreams_get (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) (time : Fin R) :
    physicalOnlineIntegersOfStreams source target U N P F exponent H T A tau online node time
      ((representatives node.1).get representative).1 ((representatives node.1).get representative).2 =
      (online node representative time).val := by
  unfold physicalOnlineIntegersOfStreams
  rw [dite_eq_left (List.get_mem _ _)]
  have heq : physicalRepresentativeFin source target U N P F A node.1
      ((representatives node.1).get representative) (List.get_mem _ _) = representative := by
    apply (representativeList_nodup N P F _ _).injective_get
    exact physicalRepresentativeFin_get source target U N P F A node.1 _ _
  rw [heq]

theorem physicalLocalOnline_mem_iff
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalInternalNode M J) (children : PhysicalChildTables M target.length)
    (t : ℕ) (q : TargetInterval target.length) (action : PhysicalRationalAction M target.length) :
    action ∈ physicalLocalOnline source target U N P F exponent H T A tau eta kappa
        (physicalOnlineIntegersOfStreams source target U N P F exponent H T A tau online)
        node.1 children t q ↔
      action ∈ physicalProgramOnline source target U N P F A T exponent H tau eta kappa
        online node.1 children t q := by
  have hmass : physicalLocalChildMass source target U N P F A T node.1 node.2 =
      physicalBandChildMassTable source target U N P F A T node.1 node.2 := by
    funext i r
    exact physicalLocalWarmupMass_eq source target U N P F A hsize hP hF hA hseed T
      (physicalChild node.1 node.2 i, r)
  unfold physicalLocalOnline physicalProgramOnline
  rw [dite_eq_left node.2, dite_eq_left node.2]
  rw [localOnlineCandidates_mem]
  constructor
  · rintro ⟨b, hb, hrep, hselected⟩
    obtain ⟨representative, hget⟩ := List.mem_iff_get.mp hrep
    change (representatives node.1).get representative =
      (b, roundInterval (seedGridSpacing b P) q) at hget
    have hinteger := physicalOnlineIntegersOfStreams_get source target U N P F exponent H T A tau online
      node representative (Fin.ofNat R (t - 1))
    rw [hget] at hinteger
    rw [hmass, hinteger] at hselected
    have heq := keyedOnlineCandidate_eq_physical source target U N P F exponent H T A tau eta kappa
      node representative children (t - 1) (online node representative (Fin.ofNat R (t - 1)))
    rw [hget] at heq
    rw [heq] at hselected
    apply List.mem_filterMap.mpr
    refine ⟨representative, List.mem_filter.mpr ⟨List.mem_finRange _, ?_⟩, hselected⟩
    apply decide_eq_true
    unfold physicalProgramOnlineGuard
    rw [hget]
    exact ⟨rfl, of_decide_eq_true (List.mem_filter.mp hb).2⟩
  · intro ha
    obtain ⟨representative, hrep, hselected⟩ := List.mem_filterMap.mp ha
    have hguard := of_decide_eq_true (List.mem_filter.mp hrep).2
    let br := (representatives node.1).get representative
    have hget : (representatives node.1).get representative =
        (br.1, roundInterval (seedGridSpacing br.1 P) q) := Prod.ext rfl hguard.1
    refine ⟨br.1, List.mem_filter.mpr ⟨?_, decide_eq_true hguard.2⟩, ?_, ?_⟩
    · exact representativeList_scale_mem _ _ (List.get_mem _ representative)
    · exact hget ▸ List.get_mem _ representative
    · have hinteger := physicalOnlineIntegersOfStreams_get source target U N P F exponent H T A tau online
        node representative (Fin.ofNat R (t - 1))
      rw [hget] at hinteger
      rw [hmass, hinteger]
      have heq := keyedOnlineCandidate_eq_physical source target U N P F exponent H T A tau eta kappa
        node representative children (t - 1) (online node representative (Fin.ofNat R (t - 1)))
      rw [hget] at heq
      exact heq.trans hselected

end Program

end EditApproximation

end OAI
