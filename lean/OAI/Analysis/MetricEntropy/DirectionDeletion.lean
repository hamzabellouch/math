import OAI.Analysis.MetricEntropy.DirectionTuples
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin

namespace OAI

universe uU

/-!
# Deleting the supports of a maximal family of bad tuples

The finite powerset construction below chooses a family of maximum cardinality.
Its maximality is proved inside the argument; it is not an input hypothesis.
Repeated indices within any tuple are allowed.
-/

namespace MetricEntropyDuality.DirectionDeletion

open scoped Classical

/-- If there are no `w` bad tuples with pairwise disjoint supports, deleting at
most `h * (w - 1)` indices removes every bad tuple. -/
theorem exists_good_subset {U : Type uU} [Fintype U] {h w : ℕ}
    (bad : (Fin h → U) → Prop) (hh : 0 < h)
    (hno : ¬ ∃ L : Fin w → Fin h → U,
      (∀ i, bad (L i)) ∧ DisjointSupports L) :
    ∃ T : Finset U, (Finset.univ \ T).card ≤ h * (w - 1) ∧
      ∀ a : Fin h → U, (∀ j, a j ∈ T) → ¬bad a := by
  classical
  let valid : Finset (Fin h → U) → Prop := fun F =>
    (∀ a ∈ F, bad a) ∧ (F : Set (Fin h → U)).PairwiseDisjoint tupleSupport
  let candidates := (Finset.univ : Finset (Fin h → U)).powerset.filter valid
  have mem_candidates (F : Finset (Fin h → U)) : F ∈ candidates ↔ valid F := by
    simp [candidates]
  have hempty : (∅ : Finset (Fin h → U)) ∈ candidates := by
    apply (mem_candidates ∅).mpr
    simp [valid]
  obtain ⟨F, hFc, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card ⟨∅, hempty⟩
  have hF : valid F := (mem_candidates F).mp hFc
  have hcard : F.card < w := by
    by_contra hn
    have hw : w ≤ F.card := Nat.le_of_not_gt hn
    obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
      (α := Fin w) (s := F) (by simpa using hw)
    apply hno
    refine ⟨fun i => e i, ?_, ?_⟩
    · intro i
      exact hF.1 (e i) (he ⟨i, rfl⟩)
    · intro i j hij
      exact hF.2 (he ⟨i, rfl⟩) (he ⟨j, rfl⟩)
        (fun heq => hij (e.injective heq))
  let deleted := F.biUnion tupleSupport
  have hdeleted : deleted.card ≤ F.card * h :=
    Finset.card_biUnion_le_card_mul F tupleSupport h
      (fun a _ => tupleSupport_card_le a)
  refine ⟨Finset.univ \ deleted, ?_, ?_⟩
  · have hcard' : F.card ≤ w - 1 := Nat.le_sub_one_of_lt hcard
    calc
      (Finset.univ \ (Finset.univ \ deleted)).card = deleted.card := by
        rw [Finset.sdiff_sdiff_self_left, Finset.univ_inter]
      _ ≤ F.card * h := hdeleted
      _ ≤ h * (w - 1) := by
        simpa only [Nat.mul_comm] using Nat.mul_le_mul_right h hcard'
  · intro a ha hbad
    have ha_deleted (j : Fin h) : a j ∉ deleted := (Finset.mem_sdiff.mp (ha j)).2
    have haF : a ∉ F := by
      intro haf
      obtain ⟨x, hx⟩ := tupleSupport_nonempty hh a
      obtain ⟨j, rfl⟩ := mem_tupleSupport.mp hx
      exact ha_deleted j (Finset.mem_biUnion.mpr ⟨a, haf, hx⟩)
    have had : ∀ b ∈ F, Disjoint (tupleSupport a) (tupleSupport b) := by
      intro b hb
      apply Finset.disjoint_left.mpr
      intro x hxa hxb
      obtain ⟨j, rfl⟩ := mem_tupleSupport.mp hxa
      exact ha_deleted j (Finset.mem_biUnion.mpr ⟨b, hb, hxb⟩)
    have hins : valid (insert a F) := by
      constructor
      · intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact hbad
        · exact hF.1 b hb
      · rw [Finset.coe_insert]
        exact Set.PairwiseDisjoint.insert_of_notMem hF.2 haF had
    have hle := hmax (insert a F) ((mem_candidates _).mpr hins)
    rw [Finset.card_insert_of_notMem haF] at hle
    exact Nat.not_succ_le_self F.card hle

end MetricEntropyDuality.DirectionDeletion

end OAI
