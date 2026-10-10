import OAI.Combinatorics.Hamiltonian.MinorModel

namespace OAI

/-! Extending disjoint connected branches to a connected vertex partition. -/

namespace Barnette
noncomputable section
open scoped Classical

namespace BranchPartition
variable {V W : Type*} [Fintype V] [Fintype W] [Nonempty V]
  (H : SimpleGraph W)

omit [Fintype W] in
lemma walk_crosses_boundary {S : Set W} {v w : W} (p : H.Walk v w)
    (hv : v ∈ S) (hw : w ∉ S) :
    ∃ a ∈ S, ∃ b ∉ S, H.Adj a b := by
  induction p with
  | nil => exact (hw hv).elim
  | @cons u z w h p ih =>
    by_cases hz : z ∈ S
    · exact ih hz hw
    · exact ⟨u, hv, z, hz, h⟩

theorem extend (hH : H.Connected) (B₀ : V → Set W)
    (hB₀ : ∀ v, (H.induce (B₀ v)).Connected)
    (hd₀ : ∀ v w, v ≠ w → Disjoint (B₀ v) (B₀ w)) :
    ∃ B : V → Set W,
      (∀ v, B₀ v ⊆ B v) ∧
      (∀ v, (H.induce (B v)).Connected) ∧
      (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ w, ∃ v, w ∈ B v) := by
  let S : Set (V → Set W) := {B | (∀ v, B₀ v ⊆ B v) ∧
    (∀ v, (H.induce (B v)).Connected) ∧
    (∀ v w, v ≠ w → Disjoint (B v) (B w))}
  let size (B : V → Set W) := (⋃ v, B v).ncard
  have hS : S.Nonempty := ⟨B₀, fun _ => Set.Subset.rfl, hB₀, hd₀⟩
  obtain ⟨B, hB, hmax⟩ := S.exists_max_image size (Set.toFinite _) hS
  refine ⟨B, hB.1, hB.2.1, hB.2.2, ?_⟩
  intro w
  by_contra hw
  have hwU : w ∉ ⋃ v, B v := by simpa only [Set.mem_iUnion] using hw
  obtain ⟨v₀⟩ := ‹Nonempty V›
  obtain ⟨a₀⟩ := (hB.2.1 v₀).nonempty
  obtain ⟨p⟩ := hH a₀.val w
  obtain ⟨a, ha, b, hb, hab⟩ := walk_crosses_boundary H p
    (Set.mem_iUnion.mpr ⟨v₀, a₀.property⟩) hwU
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp ha
  let B' : V → Set W := fun z => if z = v then insert b (B v) else B z
  have hle : ∀ z, B z ⊆ B' z := by
    intro z x hx
    by_cases hz : z = v
    · subst z; simp only [B', ite_true]; exact Set.mem_insert_of_mem _ hx
    · simpa only [B', hz, ite_false] using hx
  have hB' : B' ∈ S := by
    refine ⟨fun z => (hB.1 z).trans (hle z), ?_, ?_⟩
    · intro z
      by_cases hz : z = v
      · subst z
        have hsingle : (H.induce ({b} : Set W)).Preconnected := by
          intro x y
          have he : x = y := Subsingleton.elim _ _
          subst y
          exact .rfl
        have hh := SimpleGraph.connected_induce_union (hB.2.1 v).preconnected hsingle
          hv (show b ∈ ({b} : Set W) by simp) hab
        rw [show B' v = insert b (B v) by simp [B']]
        rw [Set.union_singleton] at hh
        exact hh
      · rw [show B' z = B z by simp [B', hz]]
        exact hB.2.1 z
    · intro z t hzt
      rw [Set.disjoint_left]
      intro x hxz hxt
      by_cases hz : z = v
      · subst z
        have ht : t ≠ v := Ne.symm hzt
        simp only [B', ite_true, Set.mem_insert_iff] at hxz
        rw [show B' t = B t by simp only [B', ht, ite_false]] at hxt
        rcases hxz with rfl | hxz
        · exact hb (Set.mem_iUnion.mpr ⟨t, hxt⟩)
        · exact Set.disjoint_left.mp (hB.2.2 v t hzt) hxz hxt
      · rw [show B' z = B z by simp only [B', hz, ite_false]] at hxz
        by_cases ht : t = v
        · subst t
          simp only [B', ite_true, Set.mem_insert_iff] at hxt
          rcases hxt with rfl | hxt
          · exact hb (Set.mem_iUnion.mpr ⟨z, hxz⟩)
          · exact Set.disjoint_left.mp (hB.2.2 z v hzt) hxz hxt
        · rw [show B' t = B t by simp only [B', ht, ite_false]] at hxt
          exact Set.disjoint_left.mp (hB.2.2 z t hzt) hxz hxt
  have hstrict : (⋃ z, B z) ⊂ ⋃ z, B' z := by
    refine ⟨Set.iUnion_mono hle, ?_⟩
    intro hh
    apply hb (hh ?_)
    exact Set.mem_iUnion.mpr ⟨v, by simp [B']⟩
  exact (not_lt_of_ge (hmax B' hB')) (Set.ncard_lt_ncard hstrict)

omit [Fintype V] [Fintype W] [Nonempty V] in

theorem quotient (B : V → Set W)
    (hB : ∀ v, (H.induce (B v)).Connected)
    (hd : ∀ v w, v ≠ w → Disjoint (B v) (B w))
    (hcover : ∀ w, ∃ v, w ∈ B v) :
    ∃ q : W → V, Function.Surjective q ∧ (∀ w v, q w = v ↔ w ∈ B v) := by
  choose q hq using hcover
  have he (w : W) (v : V) : q w = v ↔ w ∈ B v := by
    constructor
    · intro hv; exact hv ▸ hq w
    · intro hw
      by_contra hne
      exact Set.disjoint_left.mp (hd (q w) v hne) (hq w) hw
  refine ⟨q, ?_, he⟩
  intro v
  obtain ⟨w⟩ := (hB v).nonempty
  exact ⟨w.val, (he w.val v).mpr w.property⟩

end BranchPartition
end
end Barnette

end OAI
