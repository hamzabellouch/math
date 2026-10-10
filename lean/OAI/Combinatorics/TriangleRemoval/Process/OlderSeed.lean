import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.TriangleGrowth
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {N R : ℕ}
variable (A : TriangleGrowth G N R)

lemma older_eq_seed {v : Fin N} (hv : v.val < R) : A.older v = A.seed.older v := by
  rw [older,dite_eq_right (Nat.not_le_of_gt hv)]

lemma nonroot_of_card_two {v : Fin N} (hv : (A.older v).card = 2) : R ≤ v.val := by
  by_contra hn
  have hh := A.seed_small v (Nat.lt_of_not_ge hn)
  rw [← A.older_eq_seed (Nat.lt_of_not_ge hn),hv] at hh
  omega

lemma parent_label_mem {v p : Fin N} (hv : R ≤ v.val) (hp : A.parent v = some p) :
    A.label p ∈ A.attach v := by
  by_contra hn
  have hs : A.attach v ⊆ A.attach p := by
    intro x hx
    exact (Finset.mem_insert.mp ((A.child_attach v p hv hp).1 hx)).resolve_left
      (fun h => hn (h ▸ hx))
  have he : A.attach v = A.attach p := Finset.eq_of_subset_of_card_le hs (by
    rw [A.attach_card v hv,A.attach_card p (A.parent_nonroot v p hv hp)])
  exact (A.child_attach v p hv hp).2 he

lemma parent_mem_older {v p : Fin N} (hv : R ≤ v.val) (hp : A.parent v = some p) :
    p ∈ A.older v := by
  rw [older,dite_eq_left hv,hp]
  exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _,A.parent_label_mem hv hp⟩

lemma older_le_parent {v p x : Fin N} (hv : R ≤ v.val) (hp : A.parent v = some p)
    (hx : x ∈ A.older v) : x ≤ p := by
  rw [older,dite_eq_left hv,hp] at hx
  rcases Finset.mem_insert.mp (Finset.mem_filter.mp hx).1 with h | h
  · exact le_of_eq h
  · exact le_of_lt ((A.older_invariants p).1 x h)

lemma older_root_of_none {v x : Fin N} (hv : R ≤ v.val) (hp : A.parent v = none)
    (hx : x ∈ A.older v) : x.val < R := by
  rw [older,dite_eq_left hv,hp] at hx
  exact (A.mem_roots x).mp (Finset.mem_filter.mp hx).1

lemma parent_of_max {v p : Fin N} (hv : R ≤ v.val) (hp : R ≤ p.val)
    (hpm : p ∈ A.older v) (hmax : ∀ x ∈ A.older v, x ≤ p) : A.parent v = some p := by
  cases hpar : A.parent v with
  | none =>
    have hh := A.older_root_of_none hv hpar hpm
    omega
  | some q =>
    have hq := hmax q (A.parent_mem_older hv hpar)
    have hqp := A.older_le_parent hv hpar hpm
    exact congrArg some (le_antisymm hq hqp)

lemma root_graph {x y : Fin N} (hx : x.val < R) (hy : y.val < R) :
    A.birthGraph.graph.Adj x y ↔ A.seed.graph.Adj x y := by
  change (x ∈ A.older y ∨ y ∈ A.older x) ↔ _
  rw [A.older_eq_seed hx,A.older_eq_seed hy]
  rfl

lemma older_pair_of_root {v : Fin N} (hv : R ≤ v.val) (hp : A.parent v = none) :
    ∃ x y : Fin N, x.val < R ∧ y.val < R ∧ A.seed.graph.Adj x y ∧
      A.older v = {x,y} := by
  obtain ⟨x,y,hx,hy,hxy,hat⟩ := A.root_attach v hv hp
  refine ⟨x,y,hx,hy,hxy,?_⟩
  have hxm : x ∈ A.older v := by
    rw [older,dite_eq_left hv,hp]
    exact Finset.mem_filter.mpr ⟨(A.mem_roots x).mpr hx,by rw [hat]; simp⟩
  have hym : y ∈ A.older v := by
    rw [older,dite_eq_left hv,hp]
    exact Finset.mem_filter.mpr ⟨(A.mem_roots y).mpr hy,by rw [hat]; simp⟩
  exact A.birthGraph.older_eq_pair hxy.ne hxm hym

theorem spawnRules : A.birthGraph.SpawnRules G A.label := by
  constructor
  · have hold (u v : Fin N) (h : u ∈ A.older v) : G.Adj (A.label u) (A.label v) := by
      by_cases hv : R ≤ v.val
      · have hm : A.label u ∈ A.attach v := by
          rw [← ((A.older_invariants v).2 hv).2.1]
          exact Finset.mem_image.mpr ⟨u,h,rfl⟩
        exact (A.triangle v hv).2 _ (Finset.mem_insert_of_mem hm) _
          (Finset.mem_insert_self _ _) (fun he => A.new_label v hv (he ▸ hm))
      · rw [A.older_eq_seed (Nat.lt_of_not_ge hv)] at h
        exact A.seed_labels v (Nat.lt_of_not_ge hv) u h
    intro a b h
    rcases h with h | h
    · exact hold a b h
    · exact (hold b a h).symm
  · intro v hvc a ha b hb hab
    have hv := A.nonroot_of_card_two hvc
    cases hp : A.parent v with
    | none =>
      obtain ⟨x,y,hx,hy,hxy,he⟩ := A.older_pair_of_root hv hp
      have hg := (A.root_graph hx hy).mpr hxy
      change a ∈ A.older v at ha
      change b ∈ A.older v at hb
      rw [he] at ha hb
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact hg
      · exact hg.symm
      · exact False.elim (hab rfl)
    | some p =>
      have he := A.birthGraph.older_eq_pair hab ha hb
      have hpm := A.parent_mem_older hv hp
      change p ∈ A.birthGraph.older v at hpm
      rw [he] at hpm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hpm
      have hsub : A.older v ⊆ insert p (A.older p) := by
        rw [older,dite_eq_left hv,hp]
        exact Finset.filter_subset _ _
      rcases hpm with hpa | hpb
      · subst a
        exact Or.inr ((Finset.mem_insert.mp (hsub hb)).resolve_left hab.symm)
      · subst b
        exact Or.inl ((Finset.mem_insert.mp (hsub ha)).resolve_left hab)
  · intro v p hpm hmax hpc
    have hp := A.nonroot_of_card_two hpc
    have hv : R ≤ v.val := le_trans hp (le_of_lt (A.birthGraph.older_lt v p hpm))
    have hpar := A.parent_of_max hv hp hpm hmax
    rw [A.parentType_eq v hv,A.parentType_eq p hp]
    exact A.omission v p hv hpar
  · intro v w hvc he hl
    change A.older v = A.older w at he
    change (A.older v).card = 2 at hvc
    have hv := A.nonroot_of_card_two hvc
    have hw := A.nonroot_of_card_two (he ▸ hvc)
    have hp : A.parent v = A.parent w := by
      cases hpv : A.parent v with
      | none =>
        cases hpw : A.parent w with
        | none => rfl
        | some p =>
          have hm := A.parent_mem_older hw hpw
          rw [← he] at hm
          have hpr := A.older_root_of_none hv hpv hm
          have hpn := A.parent_nonroot w p hw hpw
          omega
      | some p =>
        have hpm := A.parent_mem_older hv hpv
        have hmax := fun x (hx : x ∈ A.older v) => A.older_le_parent hv hpv hx
        have hpm' : p ∈ A.older w := he ▸ hpm
        have hmax' : ∀ x ∈ A.older w, x ≤ p := by
          intro x hx
          exact hmax x (he.symm ▸ hx)
        exact (A.parent_of_max hw (A.parent_nonroot v p hv hpv) hpm' hmax').symm
    apply A.distinct_children v w hv hw hp _ hl
    rw [← ((A.older_invariants v).2 hv).2.1,← ((A.older_invariants w).2 hw).2.1]
    exact congrArg (Finset.image A.label) he

end SharpTerminalLeave.TriangleGrowth

end

end OAI
