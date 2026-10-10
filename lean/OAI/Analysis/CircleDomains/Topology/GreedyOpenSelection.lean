import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Nat
import Mathlib.Data.Set.Card
import Mathlib.Order.Monotone.Basic

namespace OAI

/-!
# Countable selection of compatible open barriers

A basis enumeration selects one admissible candidate at each finite stage.
If removing previous candidates allows a candidate with the same or larger open set,
every candidate
admissible for the final family has its open set covered by that family.
This is the selection step only; countability of unavailable ends is separate.
-/

open Set Function

noncomputable section

namespace CircleDomainRigidity

variable {X C : Type*}

private def greedyStep (B : ℕ → Set X) (U : C → Set X)
    (Allowed : Set C → C → Prop) (n : ℕ) (A : Set C) : Set C := by
  classical
  exact if h : ∃ c, Allowed A c ∧ B n ⊆ U c then insert h.choose A else A

private theorem greedyStep_contains (B : ℕ → Set X) (U : C → Set X)
    (Allowed : Set C → C → Prop) (n : ℕ) (A : Set C) :
    A ⊆ greedyStep B U Allowed n A := by
  classical
  unfold greedyStep
  split
  · exact subset_insert _ _
  · exact Subset.refl _

private theorem greedyStep_finite (B : ℕ → Set X) (U : C → Set X)
    (Allowed : Set C → C → Prop) (n : ℕ) {A : Set C} (hA : A.Finite) :
    (greedyStep B U Allowed n A).Finite := by
  classical
  unfold greedyStep
  split
  · exact hA.insert _
  · exact hA

private theorem greedyStep_new_subsingleton (B : ℕ → Set X) (U : C → Set X)
    (Allowed : Set C → C → Prop) (n : ℕ) (A : Set C) :
    (greedyStep B U Allowed n A \ A).Subsingleton := by
  classical
  unfold greedyStep
  split
  · intro c hc d hd
    exact (hc.1.resolve_right hc.2).trans (hd.1.resolve_right hd.2).symm
  · intro c hc
    exact (hc.2 hc.1).elim

/-- Select a countable compatible family whose union covers every finally
admissible candidate. The stage condition retains the actual order of selection. -/
theorem exists_countable_open_selection [TopologicalSpace X] [SecondCountableTopology X]
    (U : C → Set X) (hU : ∀ c, IsOpen (U c))
    (Allowed : Set C → C → Prop)
    (hrestrict : ∀ {A D : Set C}, A ⊆ D → ∀ c, Allowed D c →
      ∃ d, Allowed A d ∧ U c ⊆ U d) :
    ∃ A : ℕ → Set C,
      A 0 = ∅ ∧ (∀ n, (A n).Finite) ∧ Monotone A ∧
      (∀ n, (A (n + 1) \ A n).Subsingleton) ∧
      (∀ n c, c ∈ A (n + 1) \ A n → Allowed (A n) c) ∧
      (⋃ n, A n).Countable ∧
      ∀ c, Allowed (⋃ n, A n) c → U c ⊆ ⋃ d ∈ ⋃ n, A n, U d := by
  classical
  obtain ⟨B, hB⟩ := TopologicalSpace.exists_seq_basis X
  let A : ℕ → Set C := Nat.rec ∅ (fun n D => greedyStep B U Allowed n D)
  have hstep (n : ℕ) : A (n + 1) = greedyStep B U Allowed n (A n) := rfl
  have hmono : Monotone A := monotone_nat_of_le_succ fun n =>
    greedyStep_contains B U Allowed n (A n)
  have hfin (n : ℕ) : (A n).Finite := by
    induction n with
    | zero => exact finite_empty
    | succ n ih => exact greedyStep_finite B U Allowed n ih
  refine ⟨A, rfl, hfin, hmono, fun n => greedyStep_new_subsingleton B U Allowed n (A n),
    ?_, countable_iUnion fun n => (hfin n).countable, ?_⟩
  · intro n c hc
    rw [hstep] at hc
    unfold greedyStep at hc
    split at hc
    · rename_i h
      have he : c = h.choose := hc.1.resolve_right hc.2
      subst c
      exact h.choose_spec.1
    · exact (hc.2 hc.1).elim
  · intro c hc x hx
    obtain ⟨V, hV, hxV, hVU⟩ := hB.exists_subset_of_mem_open hx (hU c)
    obtain ⟨n, rfl⟩ := hV
    obtain ⟨d, hd, hcd⟩ := hrestrict (subset_iUnion A n) c hc
    have hn : ∃ d, Allowed (A n) d ∧ B n ⊆ U d := ⟨d, hd, hVU.trans hcd⟩
    have hchosen : hn.choose ∈ A (n + 1) := by
      rw [hstep]
      simp only [greedyStep, dite_eq_left hn, mem_insert_iff, true_or]
    exact mem_iUnion₂.mpr ⟨hn.choose, mem_iUnion.mpr ⟨n + 1, hchosen⟩, hn.choose_spec.2 hxV⟩
/-- The open-set selection can impose every countably indexed accuracy demand
at once, retaining compatibility across different accuracies. -/
theorem exists_countable_graded_open_selection
    [TopologicalSpace X] [SecondCountableTopology X]
    (U : C → Set X) (hU : ∀ c, IsOpen (U c)) (grade : C → ℕ)
    (Allowed : Set C → C → Prop)
    (hrestrict : ∀ {A D : Set C}, A ⊆ D → ∀ c, Allowed D c →
      ∃ d, Allowed A d ∧ grade d = grade c ∧ U c ⊆ U d) :
    ∃ A : ℕ → Set C,
      A 0 = ∅ ∧ (∀ n, (A n).Finite) ∧ Monotone A ∧
      (∀ n, (A (n + 1) \ A n).Subsingleton) ∧
      (∀ n c, c ∈ A (n + 1) \ A n → Allowed (A n) c) ∧
      (⋃ n, A n).Countable ∧
      ∀ c, Allowed (⋃ n, A n) c → ∀ x ∈ U c,
        ∃ d ∈ ⋃ n, A n, grade d = grade c ∧ x ∈ U d := by
  let V : C → Set (ℕ × X) := fun c => {grade c} ×ˢ U c
  have hV (c : C) : IsOpen (V c) := (isOpen_discrete _).prod (hU c)
  have hres {A D : Set C} (hAD : A ⊆ D) (c : C) (hc : Allowed D c) :
      ∃ d, Allowed A d ∧ V c ⊆ V d := by
    obtain ⟨d, hd, hg, hcd⟩ := hrestrict hAD c hc
    refine ⟨d, hd, ?_⟩
    intro p hp
    exact ⟨by simpa only [V, mem_prod, mem_singleton_iff, hg] using hp.1, hcd hp.2⟩
  obtain ⟨A, h0, hfin, hmono, hsingle, hnew, hcount, hcover⟩ :=
    exists_countable_open_selection V hV Allowed hres
  refine ⟨A, h0, hfin, hmono, hsingle, hnew, hcount, ?_⟩
  intro c hc x hx
  obtain ⟨d, hd, hp⟩ := mem_iUnion₂.mp (hcover c hc (show (grade c, x) ∈ V c from ⟨rfl, hx⟩))
  exact ⟨d, hd, hp.1.symm, hp.2⟩

/-- If only countably many endpoints lack an admissible test at each accuracy,
the graded selection leaves only countably many endpoints uncovered. The
hypothesis is precisely where the separate path-law argument is needed. -/
theorem exists_countable_graded_cover
    [TopologicalSpace X] [SecondCountableTopology X]
    (U : C → Set X) (hU : ∀ c, IsOpen (U c)) (grade : C → ℕ)
    (Allowed : Set C → C → Prop)
    (hrestrict : ∀ {A D : Set C}, A ⊆ D → ∀ c, Allowed D c →
      ∃ d, Allowed A d ∧ grade d = grade c ∧ U c ⊆ U d)
    (hunavailable : ∀ A : Set C, A.Countable → ∀ k : ℕ,
      {x | ¬∃ c, Allowed A c ∧ grade c = k ∧ x ∈ U c}.Countable) :
    ∃ A : ℕ → Set C,
      A 0 = ∅ ∧ (∀ n, (A n).Finite) ∧ Monotone A ∧
      (∀ n, (A (n + 1) \ A n).Subsingleton) ∧
      (∀ n c, c ∈ A (n + 1) \ A n → Allowed (A n) c) ∧
      (⋃ n, A n).Countable ∧
      ∃ S : Set X, S.Countable ∧ ∀ x ∉ S, ∀ k,
        ∃ c ∈ ⋃ n, A n, grade c = k ∧ x ∈ U c := by
  classical
  obtain ⟨A, h0, hfin, hmono, hsingle, hnew, hcount, hcover⟩ :=
    exists_countable_graded_open_selection U hU grade Allowed hrestrict
  let S : Set X := ⋃ k : ℕ, {x | ¬∃ c, Allowed (⋃ n, A n) c ∧ grade c = k ∧ x ∈ U c}
  refine ⟨A, h0, hfin, hmono, hsingle, hnew, hcount, S,
    countable_iUnion (fun k => hunavailable _ hcount k), ?_⟩
  intro x hx k
  have hav : ∃ c, Allowed (⋃ n, A n) c ∧ grade c = k ∧ x ∈ U c := by
    by_contra h
    exact hx (mem_iUnion.mpr ⟨k, h⟩)
  obtain ⟨c, hc, hg, hxc⟩ := hav
  obtain ⟨d, hd, hgd, hxd⟩ := hcover c hc x hxc
  exact ⟨d, hd, hgd.trans hg, hxd⟩

end CircleDomainRigidity

end

end OAI
