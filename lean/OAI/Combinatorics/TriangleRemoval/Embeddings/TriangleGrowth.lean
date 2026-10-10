import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.BirthGraph

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

structure TriangleGrowth {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (N R : ℕ) where
  label : Fin N → V
  seed : BirthGraph N
  seed_small : ∀ v, v.val < R → (seed.older v).card ≤ 1
  seed_root : ∀ v, ∀ u ∈ seed.older v, v.val < R → u.val < R
  seed_labels : ∀ v, v.val < R → ∀ u ∈ seed.older v, G.Adj (label u) (label v)
  roots_injective : Set.InjOn label {v | v.val < R}
  attach : Fin N → Finset V
  parent : Fin N → Option (Fin N)
  parent_lt : ∀ v p, R ≤ v.val → parent v = some p → p < v
  parent_nonroot : ∀ v p, R ≤ v.val → parent v = some p → R ≤ p.val
  attach_card : ∀ v, R ≤ v.val → (attach v).card = 2
  new_label : ∀ v, R ≤ v.val → label v ∉ attach v
  triangle : ∀ v, R ≤ v.val → BirthGraph.IsTriangle G (insert (label v) (attach v))
  root_attach : ∀ v, R ≤ v.val → parent v = none →
    ∃ x y : Fin N, x.val < R ∧ y.val < R ∧ seed.graph.Adj x y ∧
      attach v = {label x, label y}
  child_attach : ∀ v p, R ≤ v.val → parent v = some p →
    attach v ⊆ insert (label p) (attach p) ∧ attach v ≠ attach p
  omission : ∀ v p, R ≤ v.val → parent v = some p →
    insert (label v) (attach v) ≠ insert (label p) (attach p)
  distinct_children : ∀ v w, R ≤ v.val → R ≤ w.val → parent v = parent w →
    attach v = attach w → label v = label w → v = w

namespace TriangleGrowth
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {N R : ℕ}
variable (A : TriangleGrowth G N R)

noncomputable def roots (_A : TriangleGrowth G N R) : Finset (Fin N) := Finset.univ.filter (fun v => v.val < R)

@[simp] theorem mem_roots (v : Fin N) : v ∈ A.roots ↔ v.val < R := by
  simp [roots]

noncomputable def older (A : TriangleGrowth G N R) (v : Fin N) : Finset (Fin N) :=
  if _hv : R ≤ v.val then
    match _hp : A.parent v with
    | none => A.roots.filter (fun x => A.label x ∈ A.attach v)
    | some p => (insert p (A.older p)).filter (fun x => A.label x ∈ A.attach v)
  else A.seed.older v
termination_by v.val
decreasing_by exact A.parent_lt v p _hv _hp

lemma lifted_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (s : Finset α) (t : Finset β)
    (ht : t ⊆ s.image f) : (s.filter (fun x => f x ∈ t)).image f = t := by
  ext y
  constructor
  · rintro h
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hx).2
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (ht hy)
    exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hy⟩,rfl⟩

lemma lifted_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (s : Finset α) (t : Finset β)
    (hi : Set.InjOn f s) (ht : t ⊆ s.image f) :
    (s.filter (fun x => f x ∈ t)).card = t.card := by
  have hi' : Set.InjOn f (s.filter (fun x => f x ∈ t)) :=
    hi.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  have hc : ((s.filter (fun x => f x ∈ t)).image f).card =
      (s.filter (fun x => f x ∈ t)).card := Finset.card_image_iff.mpr hi'
  rw [lifted_image f s t ht] at hc
  exact hc.symm

theorem older_invariants (v : Fin N) :
    (∀ x ∈ A.older v, x < v) ∧
    (R ≤ v.val → (A.older v).card = 2 ∧ (A.older v).image A.label = A.attach v ∧
      Set.InjOn A.label (insert v (A.older v) : Finset (Fin N))) := by
  induction v using (measure (fun v : Fin N => v.val)).wf.induction with
  | h v ih =>
    by_cases hv : R ≤ v.val
    · have main :
        (∀ x ∈ A.older v, x < v) ∧ (A.older v).card = 2 ∧
        (A.older v).image A.label = A.attach v ∧ Set.InjOn A.label (A.older v) := by
        cases hp : A.parent v with
        | none =>
          obtain ⟨x,y,hx,hy,_,hat⟩ := A.root_attach v hv hp
          have hs : A.attach v ⊆ A.roots.image A.label := by
            rw [hat]
            intro z hz
            simp only [Finset.mem_insert,Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact Finset.mem_image.mpr ⟨x,A.mem_roots x |>.mpr hx,rfl⟩
            · exact Finset.mem_image.mpr ⟨y,A.mem_roots y |>.mpr hy,rfl⟩
          have hi : Set.InjOn A.label A.roots := by
            intro x hx y hy he
            exact A.roots_injective ((A.mem_roots x).mp hx) ((A.mem_roots y).mp hy) he
          rw [older,dite_eq_left hv,hp]
          refine ⟨?_,?_,lifted_image _ _ _ hs,?_⟩
          · intro z hz
            have hzR := (A.mem_roots z).mp (Finset.mem_filter.mp hz).1
            change z.val < v.val
            exact lt_of_lt_of_le hzR hv
          · rw [lifted_card _ _ _ hi hs,A.attach_card v hv]
          · exact hi.mono (by intro z hz; exact (Finset.mem_filter.mp hz).1)
        | some p =>
          have hpv := A.parent_lt v p hv hp
          have hpR := A.parent_nonroot v p hv hp
          have hind := ih p hpv
          have hpim : (insert p (A.older p)).image A.label =
              insert (A.label p) (A.attach p) := by
            rw [Finset.image_insert,(hind.2 hpR).2.1]
          have hs : A.attach v ⊆ (insert p (A.older p)).image A.label := by
            rw [hpim]
            exact (A.child_attach v p hv hp).1
          have hi := (hind.2 hpR).2.2
          rw [older,dite_eq_left hv,hp]
          refine ⟨?_,?_,lifted_image _ _ _ hs,?_⟩
          · intro z hz
            rcases Finset.mem_insert.mp (Finset.mem_filter.mp hz).1 with rfl | hz
            · exact hpv
            · exact (hind.1 z hz).trans hpv
          · rw [lifted_card _ _ _ hi hs,A.attach_card v hv]
          · exact hi.mono (by intro z hz; exact (Finset.mem_filter.mp hz).1)
      refine ⟨main.1,fun _ => ⟨main.2.1,main.2.2.1,?_⟩⟩
      intro x hx y hy he
      by_cases hxv : x = v <;> by_cases hyv : y = v
      · exact hxv.trans hyv.symm
      · subst x
        have hy' := (Finset.mem_insert.mp hy).resolve_left hyv
        have hm : A.label y ∈ A.attach v := by
          rw [← main.2.2.1]
          exact Finset.mem_image.mpr ⟨y,hy',rfl⟩
        exact False.elim (A.new_label v hv (he.symm ▸ hm))
      · subst y
        have hx' := (Finset.mem_insert.mp hx).resolve_left hxv
        have hm : A.label x ∈ A.attach v := by
          rw [← main.2.2.1]
          exact Finset.mem_image.mpr ⟨x,hx',rfl⟩
        exact False.elim (A.new_label v hv (he ▸ hm))
      · exact main.2.2.2 ((Finset.mem_insert.mp hx).resolve_left hxv)
          ((Finset.mem_insert.mp hy).resolve_left hyv) he
    · rw [older,dite_eq_right hv]
      exact ⟨A.seed.older_lt v,fun h => False.elim (hv h)⟩

noncomputable def birthGraph : BirthGraph N where
  older := A.older
  older_lt := fun v => (A.older_invariants v).1
  older_card := by
    intro v
    by_cases hv : R ≤ v.val
    · exact le_of_eq ((A.older_invariants v).2 hv).1
    · rw [older,dite_eq_right hv]
      exact (A.seed_small v (Nat.lt_of_not_ge hv)).trans (by omega)

@[simp] theorem parentType_eq (v : Fin N) (hv : R ≤ v.val) :
    A.birthGraph.parentType A.label v = insert (A.label v) (A.attach v) := by
  change (insert v (A.older v)).image A.label = _
  rw [Finset.image_insert,((A.older_invariants v).2 hv).2.1]

end TriangleGrowth
end SharpTerminalLeave

end

end OAI
