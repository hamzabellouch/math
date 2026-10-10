import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionBits
import OAI.Combinatorics.KMedianRecovery.Recovery.BestFallback

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Completion Categorical FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

namespace Comparison
variable {D S O : Finset V}

theorem successful_favorable_probability {L : Type*} [Fintype L] [DecidableEq L]
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
      (3/197:ℝ) ≤ probability (fun bits =>
        realCost D (out bits) ≤ (197/100:ℝ)*comparisonCost D C.assign) := by
  obtain ⟨out,hout,hmn⟩ := C.successful_favorable_completion hD Δ s hs hΔ hP hm hI hN
    F hSF hOF hS hbound colors hcolors label hcard hinj
  refine ⟨out,hout,completion_constant_success (fun bits => realCost D (out bits))
    (comparisonCost D C.assign) hP (fun bits => ?_) ?_⟩
  · unfold realCost
    rw [dite_eq_left (hout bits).2.2]
    exact Finset.sum_nonneg (fun p _ => distanceTo_nonneg _ _ _)
  · exact hmn.trans (mul_le_mul_of_nonneg_right (by norm_num :
      (240258179/125000000:ℝ) ≤ 97/50) hP.le)

end Comparison
end MetricKMedianRecovery.Sampling

namespace MetricKMedianRecovery.Sampling
open Completion Categorical FiniteSampling Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def branchScore (D S : Finset V) (Δ : ℝ) (s : State V) (u v : V) : ℝ :=
  assignmentWeight D (completionAssignment S Δ s) u * dist u v

structure BranchReady (F S : Finset V) (s : State V) (colors : V → Fin 3)
    (q c ell : ℕ) : Prop where
  deleted : s.deleted ⊆ S
  balls : ∀ i, (ballSet F (leafCenter s) (leafRadius s) i).Nonempty
  radius : ∀ i, 0 ≤ leafRadius s i
  redCount : q ≤ (colorClass (S \ s.deleted) colors 1).card
  counter : s.leaves.length+c ≤ s.deleted.card+q+ell

noncomputable def branchObjective {L : Type*} [Fintype L] [DecidableEq L]
    (D F S : Finset V) (Δ : ℝ) (s : State V) (colors : V → Fin 3)
    (label : V → L) (q c : ℕ)
    (P : BlueSubsetDP.Plan (colorClass (S \ s.deleted) colors 2) F label
      (branchScore D S Δ s) c) : Finset (CopiedBall F (leafCenter s) (leafRadius s)) → ℝ :=
  surrogate (P := ↥D) (∑ l, branchScore D S Δ s (P.sel l) (P.dst l)) q
    (fun p => virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p)
    (fun p e => dist (p : V) (copiedLoc F (leafCenter s) (leafRadius s) e))
    (fun r : ↥(colorClass (S \ s.deleted) colors 1) =>
      assignmentWeight D (completionAssignment S Δ s) (r:V))
    (fun r : ↥(colorClass (S \ s.deleted) colors 1) =>
      virtualNearest (colorClass (S \ s.deleted) colors 0) (leafCenter s) (leafRadius s) Δ (r:V))
    (fun r e => dist (r : V) (copiedLoc F (leafCenter s) (leafRadius s) e))

lemma observable_branch_exists {L : Type*} [Fintype L] [DecidableEq L]
    (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (colors : V → Fin 3) (label : V → L) (q c : ℕ)
    (P : BlueSubsetDP.Plan (colorClass (S \ s.deleted) colors 2) F label
      (branchScore D S Δ s) c)
    (h : BranchReady F S s colors q c (Fintype.card L)) :
    ∃ out : CompletionBits F s → Finset V,
      (∀ bits, out bits ⊆ F ∧ (out bits).card = S.card ∧ (out bits).Nonempty) ∧
      ∀ X, PartitionFeasible (copiedPart F (leafCenter s) (leafRadius s)) X →
        average (fun bits => realCost D (out bits)) ≤
          (19/50:ℝ) * branchObjective D F S Δ s colors label q c P ∅ +
          (1-19/50:ℝ) * branchObjective D F S Δ s colors label q c P X := by
  classical
  let red := colorClass (S \ s.deleted) colors 1
  let G := colorClass (S \ s.deleted) colors 0
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
  have hp : Function.Surjective (copiedPart F (leafCenter s) (leafRadius s)) := by
    intro i
    obtain ⟨v,hv⟩ := h.balls i
    exact ⟨⟨i,⟨v,hv⟩⟩,rfl⟩
  have ht : 1/Real.exp 1 < (19/50:ℝ) := by
    apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
    nlinarith [Real.exp_one_gt_d9]
  exact sampled_metric_branch_with_assignment D F S s.deleted G hSF hS h.deleted
    (copiedPart F (leafCenter s) (leafRadius s)) hp
    (copiedLoc F (leafCenter s) (leafRadius s)) (leafCenter s) (leafRadius s) Δ
    (completionAssignment S Δ s) (completionAssignment_mem S Δ s)
    (completionAssignment_distance S Δ s) h.radius hΔ (copiedLoc_mem F _ _)
    (copiedLoc_distance F _ _) hbound (fun r : ↥red => (r:V)) P.sel P.dst
    Subtype.val_injective P.selected_injective hred hblue hRB hG hGR hGB
    (fun l => (P.selection l).2.2) P.destination_count (by simpa only [Fintype.card_coe] using h.redCount) h.counter
    (∑ l, branchScore D S Δ s (P.sel l) (P.dst l)) (by rfl) (19/50) ht

noncomputable def acceptedOutput {L : Type*} [Fintype L] [DecidableEq L]
    (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (colors : V → Fin 3) (label : V → L) (q c : ℕ)
    (P : BlueSubsetDP.Plan (colorClass (S \ s.deleted) colors 2) F label
      (branchScore D S Δ s) c)
    (h : BranchReady F S s colors q c (Fintype.card L)) : CompletionBits F s → Finset V :=
  Classical.choose (observable_branch_exists D F S hSF hS Δ hΔ hbound s colors label q c P h)

lemma acceptedOutput_spec {L : Type*} [Fintype L] [DecidableEq L]
    (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (colors : V → Fin 3) (label : V → L) (q c : ℕ)
    (P : BlueSubsetDP.Plan (colorClass (S \ s.deleted) colors 2) F label
      (branchScore D S Δ s) c)
    (h : BranchReady F S s colors q c (Fintype.card L)) :
    let out := acceptedOutput D F S hSF hS Δ hΔ hbound s colors label q c P h
    (∀ bits, out bits ⊆ F ∧ (out bits).card = S.card ∧ (out bits).Nonempty) ∧
    ∀ X, PartitionFeasible (copiedPart F (leafCenter s) (leafRadius s)) X →
      average (fun bits => realCost D (out bits)) ≤
        (19/50:ℝ) * branchObjective D F S Δ s colors label q c P ∅ +
        (1-19/50:ℝ) * branchObjective D F S Δ s colors label q c P X :=
  Classical.choose_spec (observable_branch_exists D F S hSF hS Δ hΔ hbound s colors label q c P h)

noncomputable def observableOutput {L : Type*} [Fintype L] [DecidableEq L] [Nonempty V]
    (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (colors : V → Fin 3) (label : V → L) (q c : ℕ) : CompletionBits F s → Finset V := by
  classical
  exact if h : BranchReady F S s colors q c (Fintype.card L) then
    match BlueSubsetDP.computedPlan (colorClass (S \ s.deleted) colors 2) F label
        (branchScore D S Δ s) c with
    | none => fun _ => S
    | some P => acceptedOutput D F S hSF hS Δ hΔ hbound s colors label q c P h
  else fun _ => S

lemma observableOutput_feasible {L : Type*} [Fintype L] [DecidableEq L] [Nonempty V]
    (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (colors : V → Fin 3) (label : V → L) (q c : ℕ) (bits : CompletionBits F s) :
    let out := observableOutput D F S hSF hS Δ hΔ hbound s colors label q c bits
    out ⊆ F ∧ out.card = S.card ∧ out.Nonempty := by
  classical
  dsimp only [observableOutput]
  split_ifs with h
  · cases hP : BlueSubsetDP.computedPlan (colorClass (S \ s.deleted) colors 2) F label
        (branchScore D S Δ s) c with
    | none => exact ⟨hSF,rfl,hS⟩
    | some P => exact (acceptedOutput_spec D F S hSF hS Δ hΔ hbound s colors label q c P h).1 bits
  · exact ⟨hSF,rfl,hS⟩

end MetricKMedianRecovery.Sampling

end OAI
