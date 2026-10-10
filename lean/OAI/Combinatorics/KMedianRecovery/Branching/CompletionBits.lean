import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RealizationChargingAssignment
import OAI.Combinatorics.KMedianRecovery.Recovery.BallSet
import OAI.Combinatorics.KMedianRecovery.Recovery.SubsetSubtypeRepresentative

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Completion Categorical FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable abbrev CompletionBits (F : Finset V) (s : State V) :=
  BinaryOracleIndex (CopiedBall F (leafCenter s) (leafRadius s)) s.leaves.length
    (stepExponent s.leaves.length (19/50-1/Real.exp 1))
    (sampleCount (Fintype.card (CopiedBall F (leafCenter s) (leafRadius s)))
      s.leaves.length (19/50-1/Real.exp 1)) → Bool

namespace Comparison
variable {D S O : Finset V}

theorem successful_favorable_completion {L : Type*} [Fintype L] [DecidableEq L]
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
    ∃ out : CompletionBits F s → Finset V,
      (∀ bits, out bits ⊆ F ∧ (out bits).card = S.card ∧ (out bits).Nonempty) ∧
      average (fun bits => realCost D (out bits)) ≤
        (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  classical
  have : Nonempty V := ⟨hD.choose⟩
  let dest := C.designatedDestination hD s (19/50)
  let Rstar := C.nonproxy \ s.deleted
  let redD := designatedRed Rstar dest
  let blueD := designatedBlue Rstar dest
  let Y := blueD.image (C.blueDestination hD s (19/50))
  let red := colorClass (S \ s.deleted) colors 1
  let blue := colorClass (S \ s.deleted) colors 2
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
  have hred : ∀ r : ↥red, (r:V) ∈ S \ s.deleted :=
    fun r => (Finset.mem_filter.mp r.property).1
  have hblue : ∀ l, P.sel l ∈ S \ s.deleted :=
    fun l => (Finset.mem_filter.mp (P.selection l).1).1
  have hrcolor : ∀ r : ↥red, colors r = 1 := fun r => (Finset.mem_filter.mp r.property).2
  have hbcolor : ∀ l, colors (P.sel l) = 2 := fun l => (Finset.mem_filter.mp (P.selection l).1).2
  have hRB : ∀ (r : ↥red) l, (r:V) ≠ P.sel l := by
    intro r l he
    have hh := hrcolor r
    rw [he,hbcolor l] at hh
    exact (by decide : (2 : Fin 3) ≠ 1) hh
  have hG : G ⊆ S \ s.deleted := Finset.filter_subset _ _
  have hGR : ∀ r : ↥red, (r:V) ∉ G := by
    intro r hr
    have hg := (Finset.mem_filter.mp hr).2
    rw [hrcolor r] at hg
    exact (by decide : (1 : Fin 3) ≠ 0) hg
  have hGB : ∀ l, P.sel l ∉ G := by
    intro l hl
    have hg := (Finset.mem_filter.mp hl).2
    rw [hbcolor l] at hg
    exact (by decide : (2 : Fin 3) ≠ 0) hg
  obtain ⟨hballs,X,hX,_,hcenter⟩ := copied_comparison F (leafCenter s)
    (C.coveredCenter s) (leafRadius s)
    (C.coveredCenter_facility hD (1/1000000) s hs F hOF)
    (C.coveredCenter_ball hD (1/1000000) s hs)
  have hp : Function.Surjective (copiedPart F (leafCenter s) (leafRadius s)) := by
    intro i
    obtain ⟨v,hv⟩ := hballs i
    exact ⟨⟨i,⟨v,hv⟩⟩,rfl⟩
  have hr : ∀ i, 0 ≤ leafRadius s i := fun i =>
    (hs.2.2 s.leaves[i.val] (List.getElem_mem i.isLt)).2.2.2.1.le
  have hQ : s.deleted ⊆ S := by
    intro u hu
    exact (Finset.mem_sdiff.mp (hs.1 hu)).1
  have ht : 1/Real.exp 1 < (19/50:ℝ) := by
    apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
    nlinarith [Real.exp_one_gt_d9]
  obtain ⟨out,hout,houtCost⟩ := sampled_metric_branch_with_assignment
    D F S s.deleted G hSF hS hQ (copiedPart F (leafCenter s) (leafRadius s)) hp
    (copiedLoc F (leafCenter s) (leafRadius s)) (leafCenter s) (leafRadius s) Δ
    (completionAssignment S Δ s) (completionAssignment_mem S Δ s)
    (completionAssignment_distance S Δ s) hr hΔ (copiedLoc_mem F _ _)
    (copiedLoc_distance F _ _) hbound (fun r : ↥red => (r:V)) P.sel P.dst
    Subtype.val_injective P.selected_injective hred hblue hRB hG hGR hGB
    (fun l => (P.selection l).2.2) P.destination_count hq hcount K (by rfl)
    (19/50) ht
  refine ⟨out,hout,(houtCost X hX).trans ?_⟩
  have hdisj : Disjoint (T.image Subtype.val) blueD := by
    rw [hTimage]
    exact (designated_partition Rstar dest).1
  have hcover : T.image Subtype.val ∪ blueD = C.nonproxy \ s.deleted := by
    rw [hTimage]
    exact (designated_partition Rstar dest).2
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

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
