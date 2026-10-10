import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.SuccessfulFavorableProbability

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion Categorical FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

theorem observable_successful_completion {L : Type*} [Fintype L] [DecidableEq L] [Nonempty V]
    (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (F : Finset V) (hSF : S ⊆ F) (hOF : O ⊆ F) (hS : S.Nonempty)
    (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (colors : V → Fin 3)
    (hcolors : ∀ u ∈ (C.nonproxy \ s.deleted) ∪
        designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s (19/50)),
      colors u = requiredColors (C.nonproxy \ s.deleted)
        (C.designatedDestination hD s (19/50)) u)
    (label : V → L)
    (hcard : (designatedBlue (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))).card = Fintype.card L)
    (hinj : Set.InjOn label (↑(designatedBlue (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))))) :
    let q := (designatedRed (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))).card
    let c := ((designatedBlue (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))).image (C.blueDestination hD s (19/50))).card
    average (fun bits => realCost D
      (observableOutput D F S hSF hS Δ hΔ hbound s colors label q c bits)) ≤
        (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  classical
  dsimp only
  let dest := C.designatedDestination hD s (19/50)
  let Rstar := C.nonproxy \ s.deleted
  let redD := designatedRed Rstar dest
  let blueD := designatedBlue Rstar dest
  let Y := blueD.image (C.blueDestination hD s (19/50))
  let red := colorClass (S \ s.deleted) colors 1
  let G := colorClass (S \ s.deleted) colors 0
  let score := fun u v => assignmentWeight D (completionAssignment S Δ s) u * dist u v
  obtain ⟨P,hPlan,hvalue⟩ := C.favorable_computedPlan hD s (19/50) Δ F hOF colors hcolors label hcard hinj
  let K := ∑ l, score (P.sel l) (P.dst l)
  have hcolorSub := C.favorable_color_subsets hD s (19/50) colors hcolors
  obtain ⟨T,hTimage,hTcard⟩ := subset_subtype_representative red redD hcolorSub.1
  let q := redD.card
  have hq : q ≤ Fintype.card ↥red := by
    simpa only [Fintype.card_coe] using Finset.card_le_card hcolorSub.1
  have hcount : s.leaves.length + Y.card ≤ s.deleted.card+q+Fintype.card L := by
    have hh := C.favorable_counter_bound hD s hs (19/50)
    dsimp only at hh
    change s.leaves.length+Y.card ≤ s.deleted.card+q+blueD.card at hh
    dsimp only [blueD,Rstar,dest] at hh
    rw [hcard] at hh
    exact hh
  obtain ⟨hballs,X,hX,_,hcenter⟩ := copied_comparison F (leafCenter s)
    (C.coveredCenter s) (leafRadius s)
    (C.coveredCenter_facility hD (1/1000000) s hs F hOF)
    (C.coveredCenter_ball hD (1/1000000) s hs)
  have hr : ∀ i, 0 ≤ leafRadius s i := fun i =>
    (hs.2.2 s.leaves[i.val] (List.getElem_mem i.isLt)).2.2.2.1.le
  have hQ : s.deleted ⊆ S := by
    intro u hu
    exact (Finset.mem_sdiff.mp (hs.1 hu)).1
  have hready : BranchReady F S s colors q Y.card (Fintype.card L) :=
    ⟨hQ,hballs,hr,by simpa only [Fintype.card_coe] using hq,hcount⟩
  have heq : observableOutput D F S hSF hS Δ hΔ hbound s colors label q Y.card =
      acceptedOutput D F S hSF hS Δ hΔ hbound s colors label q Y.card P hready := by
    simp only [observableOutput, dite_eq_left hready]
    have hc : BlueSubsetDP.computedPlan (colorClass (S \ s.deleted) colors 2) F label
        (branchScore D S Δ s) Y.card = some P := hPlan
    rw [hc]
  change average (fun bits => realCost D
    (observableOutput D F S hSF hS Δ hΔ hbound s colors label q Y.card bits)) ≤ _
  rw [heq]
  apply ((acceptedOutput_spec D F S hSF hS Δ hΔ hbound s colors label q Y.card P hready).2 X hX).trans
  have hdisj : Disjoint (T.image Subtype.val) blueD := by
    rw [hTimage]
    exact (designated_partition Rstar dest).1
  have hcover : T.image Subtype.val ∪ blueD = C.nonproxy \ s.deleted := by
    rw [hTimage]
    exact (designated_partition Rstar dest).2
  change (19/50:ℝ) * _ + (1-19/50:ℝ) * _ ≤ _
  apply C.surrogate_success hD Δ s hs hΔ hP hm hI hN
    (copiedLoc F (leafCenter s) (leafRadius s)) X hcenter G blueD
    (fun r : ↥red => (r:V)) Subtype.val_injective q T hTcard hdisj hcover
    _ K hvalue
  intro r hrT
  have hrD : (r:V) ∈ redD := by
    rw [← hTimage]
    exact Finset.mem_image.mpr ⟨r,hrT,rfl⟩
  have hh := C.favorable_red_rule hD (1/1000000) (19/50) s hs colors hcolors r hrD
  cases hd : selectedDestination (19/50) (C.coveredCenter s) (leafCenter s)
      (leafRadius s) (C.destinations s) (C.destinations_nonempty hD s) (r:V) with
  | proxy v => simpa only [designatedDestination,hd] using hh
  | covered i => trivial
  | uncovered v => simp only [designatedDestination,hd] at hh

end MetricKMedianRecovery.Sampling.Comparison

end OAI
