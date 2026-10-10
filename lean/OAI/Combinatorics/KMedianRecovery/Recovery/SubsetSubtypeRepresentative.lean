import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.BestDesignation
import OAI.Combinatorics.KMedianRecovery.Recovery.DestinationFacility

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [DecidableEq V]

lemma subset_subtype_representative (A B : Finset V) (hBA : B ⊆ A) :
    ∃ T : Finset ↥A, T.image Subtype.val = B ∧ T.card = B.card := by
  classical
  let T : Finset ↥A := Finset.univ.filter (fun x => (x:V) ∈ B)
  have he : T.image Subtype.val = B := by
    ext v
    constructor
    · intro h
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hr).2
    · intro hv
      refine Finset.mem_image.mpr ⟨⟨v,hBA hv⟩,?_,rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
  exact ⟨T,he,by rw [← he,Finset.card_image_of_injective _ Subtype.val_injective]⟩

end MetricKMedianRecovery.Completion
namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma nonproxy_remaining_in (C : Comparison D S O) (s : State V) :
    C.nonproxy \ s.deleted ⊆ S \ s.deleted := by
  intro u hu
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hu).1).1,
    (Finset.mem_sdiff.mp hu).2⟩

lemma favorable_color_subsets (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (colors : V → Fin 3)
    (hcolors : ∀ u ∈ (C.nonproxy \ s.deleted) ∪
        designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta),
      colors u = requiredColors (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) u) :
    designatedRed (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) ⊆
        colorClass (S \ s.deleted) colors 1 ∧
    designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) ⊆
        colorClass (S \ s.deleted) colors 2 := by
  have hh := favorable_color_consequences (C.nonproxy \ s.deleted)
    (C.designatedDestination hD s theta) (C.designation_disjoint hD s theta) colors hcolors
  exact ⟨fun u hu => Finset.mem_filter.mpr
    ⟨C.nonproxy_remaining_in s (Finset.mem_filter.mp hu).1,hh.1 u hu⟩,
    fun u hu => Finset.mem_filter.mpr
    ⟨C.nonproxy_remaining_in s (Finset.mem_filter.mp hu).1,hh.2.1 u hu⟩⟩

lemma affordable_blue_destinations (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) :
    let B := designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)
    (B.image (C.blueDestination hD s theta)).card ≤ (C.bad \ C.covered s).card ∧
    (B.image (C.blueDestination hD s theta)).card ≤ B.card := by
  classical
  dsimp only
  refine ⟨Finset.card_le_card ?_,Finset.card_image_le⟩
  intro v hv
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
  exact C.blueDestination_mem hD s theta u hu

lemma favorable_computedPlan {L : Type*} [Fintype L] [DecidableEq L] [Nonempty V]
    (C : Comparison D S O) (hD : D.Nonempty) (s : State V) (theta Δ : ℝ)
    (F : Finset V) (hOF : O ⊆ F) (colors : V → Fin 3)
    (hcolors : ∀ u ∈ (C.nonproxy \ s.deleted) ∪
        designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta),
      colors u = requiredColors (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) u)
    (label : V → L)
    (hcard : (designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)).card =
      Fintype.card L)
    (hinj : Set.InjOn label (↑(designatedBlue (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s theta)))) :
    let B := designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)
    let Y := B.image (C.blueDestination hD s theta)
    let score := fun u v => assignmentWeight D (completionAssignment S Δ s) u * dist u v
    ∃ P : BlueSubsetDP.Plan (colorClass (S \ s.deleted) colors 2) F label score Y.card,
      BlueSubsetDP.computedPlan (colorClass (S \ s.deleted) colors 2) F label score Y.card = some P ∧
      (∑ l, score (P.sel l) (P.dst l)) ≤ ∑ u ∈ B,
        assignmentWeight D (completionAssignment S Δ s) u *
        minimumMixed theta (C.coveredCenter s) (leafCenter s) (leafRadius s)
          (C.destinations s) (C.destinations_nonempty hD s) u := by
  classical
  dsimp only
  have hBF := C.favorable_color_subsets hD s theta colors hcolors
  have hYF : (designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)).image
      (C.blueDestination hD s theta) ⊆ F := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    exact hOF (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp
      (C.blueDestination_mem hD s theta u hu)).1).1
  obtain ⟨P,hP,hval⟩ := BlueSubsetDP.computedPlan_success
    (colorClass (S \ s.deleted) colors 2)
    (designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) F
    ((designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)).image
      (C.blueDestination hD s theta)) label
    (fun u v => assignmentWeight D (completionAssignment S Δ s) u * dist u v)
    (C.blueDestination hD s theta) hBF.2 hYF hcard hinj
    (fun u hu => Finset.mem_image.mpr ⟨u,hu,rfl⟩)
  refine ⟨P,hP,hval.trans_eq ?_⟩
  apply Finset.sum_congr rfl
  intro u hu
  rw [C.blueDestination_distance hD s theta u hu]

lemma favorable_counter_bound (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (hs : C.Correct hD (1/1000000) s) (theta : ℝ) :
    let dest := C.designatedDestination hD s theta
    let B := designatedBlue (C.nonproxy \ s.deleted) dest
    let R := designatedRed (C.nonproxy \ s.deleted) dest
    s.leaves.length + (B.image (C.blueDestination hD s theta)).card ≤
      s.deleted.card + R.card + B.card := by
  dsimp only
  have hh := C.exact_completion_counts hD (1/1000000) s hs
  have hc := designated_count (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)
  have hb := C.affordable_blue_destinations hD s theta
  dsimp only at hb
  omega

end MetricKMedianRecovery.Sampling.Comparison

end OAI
