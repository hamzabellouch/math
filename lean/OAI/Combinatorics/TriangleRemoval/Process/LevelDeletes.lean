import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.TreeBind

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave
namespace ExposureTree
variable {K V O A : Type*}

@[simp] theorem evaluate_exposeLabeled (ω : K → V) (key : A → K) (as : List A) :
    evaluate ω (exposeLabeled key as) = as.map (fun a => (a, ω (key a))) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [exposeLabeled, evaluate, evaluate_bind, ih, List.map_cons]

@[simp] theorem evaluate_checkNone (ω : K → V) (as : List (ExposureTree K V Bool)) :
    evaluate ω (checkNone as) = true ↔ ∀ A ∈ as, evaluate ω A = false := by
  induction as with
  | nil => simp [checkNone, evaluate]
  | cons A as ih =>
    simp only [checkNone, evaluate_bind, List.mem_cons, forall_eq_or_imp]
    cases h : evaluate ω A <;> simp [evaluate, ih]

end ExposureTree

section TimeScan
variable {ι τ : Type*} [DecidableEq ι] [Fintype τ] [DecidableEq τ]

def levelDeletes (H : τ → Finset ι) (ω : τ → ℕ) (G : Finset ι) (k : ℕ) : Finset ι :=
  (Finset.univ.filter (fun T => ω T = k ∧ H T ⊆ G)).biUnion H

def timeScan (H : τ → Finset ι) (ω : τ → ℕ) (E : Finset ι) : ℕ → Finset ι
  | 0 => E
  | k + 1 => timeScan H ω E k \ levelDeletes H ω (timeScan H ω E k) k

omit [DecidableEq τ] in
@[simp] theorem mem_levelDeletes (H : τ → Finset ι) (ω : τ → ℕ) (G : Finset ι) (k : ℕ)
    (e : ι) : e ∈ levelDeletes H ω G k ↔ ∃ T, ω T = k ∧ H T ⊆ G ∧ e ∈ H T := by
  simp only [levelDeletes, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and]
  aesop

omit [DecidableEq τ] in
theorem timeScan_subset_initial (H : τ → Finset ι) (ω : τ → ℕ) (E : Finset ι) (k : ℕ) :
    timeScan H ω E k ⊆ E := by
  induction k with
  | zero => exact Finset.Subset.refl E
  | succ k ih => exact Finset.sdiff_subset.trans ih

omit [DecidableEq τ] in

theorem timeScan_mem_iff (H : τ → Finset ι) (ω : τ → ℕ) (E : Finset ι) (k : ℕ) (e : ι) :
    e ∈ timeScan H ω E k ↔ e ∈ E ∧
      ∀ T, ω T < k → e ∈ H T → ¬ (H T).erase e ⊆ timeScan H ω E (ω T) := by
  induction k with
  | zero => simp [timeScan]
  | succ k ih =>
    simp only [timeScan, Finset.mem_sdiff, mem_levelDeletes, not_exists, not_and]
    constructor
    · intro he
      obtain ⟨heE, hePast⟩ := ih.mp he.1
      refine ⟨heE, fun T hTk heT hsub => ?_⟩
      by_cases hlt : ω T < k
      · exact hePast T hlt heT hsub
      · have ht : ω T = k := by omega
        apply he.2 T ht
        · intro f hf
          by_cases hfe : f = e
          · simpa [hfe] using he.1
          · exact (ht ▸ hsub) (Finset.mem_erase.mpr ⟨hfe, hf⟩)
        · exact heT
    · rintro ⟨heE, hePast⟩
      have hek : e ∈ timeScan H ω E k := ih.mpr ⟨heE, fun T hT => hePast T (by omega)⟩
      refine ⟨hek, fun T ht hsub heT => ?_⟩
      apply hePast T (by omega) heT
      rw [ht]
      exact (Finset.erase_subset e (H T)).trans hsub

theorem evaluate_gridQueryDepth_succ (H : τ → Finset ι) (N d k : ℕ)
    (ω : τ → Fin N) (focus : Finset ι) (parent : Option τ) :
    ExposureTree.evaluate ω (gridQueryDepth H N (d + 1) k focus parent) = true ↔
      ∀ e ∈ focus, ∀ T, e ∈ H T → some T ≠ parent → (ω T).val < k →
        ExposureTree.evaluate ω
          (gridQueryDepth H N d (ω T).val ((H T).erase e) (some T)) = false := by
  simp only [gridQueryDepth, ExposureTree.evaluate_bind, ExposureTree.evaluate_exposeLabeled,
    ExposureTree.evaluate_checkNone, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, List.mem_mergeSort, Finset.mem_toList]
  constructor
  · intro h e he T heT hp ht
    have hm : (e, T) ∈ gridCandidates H focus parent := by
      simp [gridCandidates, he, heT, hp]
    have hh := h (e, T) hm
    simpa only [ht, ↓reduceIte] using hh
  · intro h a ha
    have ha' : a.1 ∈ focus ∧ a.1 ∈ H a.2 ∧ some a.2 ≠ parent := by
      simpa [gridCandidates] using ha
    by_cases ht : (ω a.2).val < k
    · simpa only [ht, ↓reduceIte] using h a.1 ha'.1 a.2 ha'.2.1 ha'.2.2 ht
    · simp [ht, ExposureTree.evaluate]

theorem evaluate_gridQueryDepth_iff (H : τ → Finset ι) (N d k : ℕ)
    (ω : τ → Fin N) (E focus : Finset ι) (parent : Option τ)
    (hk : k ≤ d) (hfocus : focus ⊆ E) (hH : ∀ T, H T ⊆ E)
    (hparent : ∀ T, some T = parent → k ≤ (ω T).val) :
    ExposureTree.evaluate ω (gridQueryDepth H N d k focus parent) = true ↔
      focus ⊆ timeScan H (fun T => (ω T).val) E k := by
  induction d generalizing k focus parent with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    simp only [gridQueryDepth, ExposureTree.evaluate_bind, ExposureTree.evaluate,
      timeScan, true_iff]
    exact hfocus
  | succ d ih =>
    rw [evaluate_gridQueryDepth_succ]
    constructor
    · intro h e he
      apply (timeScan_mem_iff H (fun T => (ω T).val) E k e).mpr
      refine ⟨hfocus he, fun T hTk heT hsub => ?_⟩
      have hp : some T ≠ parent := by
        intro hh
        have := hparent T hh
        omega
      have hf := h e he T heT hp hTk
      have ht := (ih (ω T).val ((H T).erase e) (some T) (by omega)
        ((Finset.erase_subset e (H T)).trans (hH T)) (fun S hS => by cases Option.some.inj hS; rfl)).mpr hsub
      rw [ht] at hf
      contradiction
    · intro hs e he T heT _ hTk
      apply Bool.eq_false_iff.mpr
      intro ht
      have hsub := (ih (ω T).val ((H T).erase e) (some T) (by omega)
        ((Finset.erase_subset e (H T)).trans (hH T)) (fun S hS => by cases Option.some.inj hS; rfl)).mp ht
      exact ((timeScan_mem_iff H (fun T => (ω T).val) E k e).mp (hs he)).2 T hTk heT hsub

end TimeScan
end SharpTerminalLeave

end

end OAI
