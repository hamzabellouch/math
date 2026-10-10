import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.SuccessfulFavorableProbability

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Completion Categorical FiniteSampling Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def zeroObjective (D F S : Finset V) (Δ : ℝ) (s : State V)
    (colors : V → Fin 3) (q : ℕ) :
    Finset (CopiedBall F (leafCenter s) (leafRadius s)) → ℝ :=
  surrogate (P := ↥D) 0 q
    (fun p => virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p)
    (fun p e => dist (p : V) (copiedLoc F (leafCenter s) (leafRadius s) e))
    (fun r : ↥(colorClass (S \ s.deleted) colors 1) =>
      assignmentWeight D (completionAssignment S Δ s) (r:V))
    (fun r : ↥(colorClass (S \ s.deleted) colors 1) =>
      virtualNearest (colorClass (S \ s.deleted) colors 0) (leafCenter s) (leafRadius s) Δ (r:V))
    (fun r e => dist (r : V) (copiedLoc F (leafCenter s) (leafRadius s) e))

lemma zero_branch_exists
    (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (colors : V → Fin 3) (q : ℕ)
    (h : BranchReady F S s colors q 0 0) :
    ∃ out : CompletionBits F s → Finset V,
      (∀ bits, out bits ⊆ F ∧ (out bits).card = S.card ∧ (out bits).Nonempty) ∧
      ∀ X, PartitionFeasible (copiedPart F (leafCenter s) (leafRadius s)) X →
        average (fun bits => realCost D (out bits)) ≤
          (19/50:ℝ) * zeroObjective D F S Δ s colors q ∅ +
          (1-19/50:ℝ) * zeroObjective D F S Δ s colors q X := by
  classical
  let red := colorClass (S \ s.deleted) colors 1
  let G := colorClass (S \ s.deleted) colors 0
  have hred : ∀ r : ↥red, (r:V) ∈ S \ s.deleted :=
    fun r => (Finset.mem_filter.mp r.property).1
  have hGR : ∀ r : ↥red, (r:V) ∉ G := by
    intro r hr
    have hg := (Finset.mem_filter.mp hr).2
    have hh := (Finset.mem_filter.mp r.property).2
    rw [hh] at hg
    exact (by decide : (1 : Fin 3) ≠ 0) hg
  have hp : Function.Surjective (copiedPart F (leafCenter s) (leafRadius s)) := by
    intro i
    obtain ⟨v,hv⟩ := h.balls i
    exact ⟨⟨i,⟨v,hv⟩⟩,rfl⟩
  have ht : 1/Real.exp 1 < (19/50:ℝ) := by
    apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
    nlinarith [Real.exp_one_gt_d9]
  exact sampled_metric_branch_with_assignment (B := Fin 0) (c := 0)
    D F S s.deleted G hSF hS h.deleted
    (copiedPart F (leafCenter s) (leafRadius s)) hp
    (copiedLoc F (leafCenter s) (leafRadius s)) (leafCenter s) (leafRadius s) Δ
    (completionAssignment S Δ s) (completionAssignment_mem S Δ s)
    (completionAssignment_distance S Δ s) h.radius hΔ (copiedLoc_mem F _ _)
    (copiedLoc_distance F _ _) hbound (fun r : ↥red => (r:V)) Fin.elim0 Fin.elim0
    Subtype.val_injective (by intro i; exact i.elim0) hred (by intro i; exact i.elim0)
    (by intro _ i; exact i.elim0) (Finset.filter_subset _ _) hGR (by intro i; exact i.elim0)
    (by intro i; exact i.elim0) (by simp)
    (by simpa only [Fintype.card_coe] using h.redCount)
    (by simpa only [Fintype.card_fin] using h.counter) 0 (by simp) (19/50) ht

noncomputable def zeroAccepted
    (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (colors : V → Fin 3) (q : ℕ)
    (h : BranchReady F S s colors q 0 0) : CompletionBits F s → Finset V :=
  Classical.choose (zero_branch_exists D F S hSF hS Δ hΔ hbound s colors q h)

lemma zeroAccepted_spec
    (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (colors : V → Fin 3) (q : ℕ)
    (h : BranchReady F S s colors q 0 0) :
    let out := zeroAccepted D F S hSF hS Δ hΔ hbound s colors q h
    (∀ bits, out bits ⊆ F ∧ (out bits).card = S.card ∧ (out bits).Nonempty) ∧
      ∀ X, PartitionFeasible (copiedPart F (leafCenter s) (leafRadius s)) X →
        average (fun bits => realCost D (out bits)) ≤
          (19/50:ℝ) * zeroObjective D F S Δ s colors q ∅ +
          (1-19/50:ℝ) * zeroObjective D F S Δ s colors q X :=
  Classical.choose_spec (zero_branch_exists D F S hSF hS Δ hΔ hbound s colors q h)

noncomputable def zeroOutput
    (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (colors : V → Fin 3) (q : ℕ) : CompletionBits F s → Finset V := by
  classical
  exact if h : BranchReady F S s colors q 0 0 then
    zeroAccepted D F S hSF hS Δ hΔ hbound s colors q h else fun _ => S

lemma zeroOutput_feasible
    (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (colors : V → Fin 3) (q : ℕ) (bits : CompletionBits F s) :
    let out := zeroOutput D F S hSF hS Δ hΔ hbound s colors q bits
    out ⊆ F ∧ out.card = S.card ∧ out.Nonempty := by
  classical
  dsimp only [zeroOutput]
  split_ifs with h
  · exact (zeroAccepted_spec D F S hSF hS Δ hΔ hbound s colors q h).1 bits
  · exact ⟨hSF,rfl,hS⟩

end MetricKMedianRecovery.Sampling

end OAI
