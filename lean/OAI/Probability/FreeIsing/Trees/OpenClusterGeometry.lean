import OAI.Probability.FreeIsing.Trees.ConnectedHull
import OAI.Probability.FreeIsing.Trees.Parents

namespace OAI

noncomputable section

namespace Problem367.OpenCluster

open Relation
open ConnectedHull

variable {d : ℕ}

def openAdj (P : TreeVertex d → Prop) (u v : TreeVertex d) : Prop :=
  treeAdj u v ∧ if u.1.length < v.1.length then P v else P u

def downwardOpen (P : TreeVertex d → Prop) (r v : TreeVertex d) : Prop :=
  r.1 <+: v.1 ∧
    ∀ n : ℕ, r.1.length < n → n ≤ v.1.length → P (takeVertex v n)

lemma openAdj_symm {P : TreeVertex d → Prop} {u v : TreeVertex d}
    (h : openAdj P u v) : openAdj P v u := by
  refine ⟨h.1.symm, ?_⟩
  obtain hl | hl := treeAdj_length h.1
  · have huv : u.1.length < v.1.length := by omega
    have hvu : ¬v.1.length < u.1.length := by omega
    simpa only [ite_eq_left huv, ite_eq_right hvu] using h.2
  · have huv : ¬u.1.length < v.1.length := by omega
    have hvu : v.1.length < u.1.length := by omega
    simpa only [ite_eq_right huv, ite_eq_left hvu] using h.2

lemma reachable_symm {P : TreeVertex d → Prop} {u v : TreeVertex d}
    (h : ReflTransGen (openAdj P) u v) :
    ReflTransGen (openAdj P) v u := by
  induction h with
  | refl => exact .refl
  | tail h huv ih => exact (ReflTransGen.single (openAdj_symm huv)).trans ih

lemma open_of_crossing_prefix {P : TreeVertex d → Prop} {w u v : TreeVertex d}
    (h : openAdj P u v) (hu : ¬w.1 <+: u.1) (hv : w.1 <+: v.1) : P w := by
  rcases h.1 with ⟨c, hc⟩ | ⟨c, hc⟩
  · have huv : u.1 <+: v.1 := by rw [hc]; exact List.prefix_append _ _
    have hn : ¬w.1.length ≤ u.1.length := by
      intro hn
      exact hu (List.prefix_of_prefix_length_le hv huv hn)
    have hlen : v.1.length = u.1.length + 1 := by simp [hc]
    have hwv : w = v := by
      apply Subtype.ext
      exact hv.eq_of_length (by have := hv.length_le; omega)
    subst w
    have hlt : u.1.length < v.1.length := by omega
    simpa only [ite_eq_left hlt] using h.2
  · have hvu : v.1 <+: u.1 := by rw [hc]; exact List.prefix_append _ _
    exact False.elim (hu (hv.trans hvu))

lemma open_of_reachable_crossing_prefix {P : TreeVertex d → Prop}
    {w u v : TreeVertex d} (h : ReflTransGen (openAdj P) u v)
    (hu : ¬w.1 <+: u.1) (hv : w.1 <+: v.1) : P w := by
  induction h with
  | refl => exact False.elim (hu hv)
  | @tail a b h hab ih =>
      by_cases ha : w.1 <+: a.1
      · exact ih ha
      · exact open_of_crossing_prefix hab ha hv

lemma downwardOpen_refl (P : TreeVertex d → Prop) (r : TreeVertex d) :
    downwardOpen P r r := by
  refine ⟨List.prefix_refl _, ?_⟩
  intro n hn hnr
  omega

lemma downwardOpen_of_reachable {P : TreeVertex d → Prop} {r v : TreeVertex d}
    (h : ReflTransGen (openAdj P) r v) (hrv : r.1 <+: v.1) :
    downwardOpen P r v := by
  refine ⟨hrv, ?_⟩
  intro n hrn hnv
  apply open_of_reachable_crossing_prefix h
  · intro hpre
    have hlen : (takeVertex v n).1.length = n := by
      simp [takeVertex, Nat.min_eq_left hnv]
    have := hpre.length_le
    omega
  · exact List.take_prefix _ _

lemma prefix_of_reachable_min {P : TreeVertex d → Prop} {r v : TreeVertex d}
    (h : ReflTransGen (openAdj P) r v)
    (hmin : ∀ w, ReflTransGen (openAdj P) r w → r.1.length ≤ w.1.length) :
    r.1 <+: v.1 := by
  induction h with
  | refl => exact List.prefix_refl _
  | @tail u v h huv ih =>
      rcases huv.1 with ⟨c, hc⟩ | ⟨c, hc⟩
      · exact ih.trans (by rw [hc]; exact List.prefix_append _ _)
      · have hvu : v.1 <+: u.1 := by rw [hc]; exact List.prefix_append _ _
        exact List.prefix_of_prefix_length_le ih hvu (hmin v (h.tail huv))

lemma exists_min_reachable (P : TreeVertex d → Prop) (o : TreeVertex d) :
    ∃ r, ReflTransGen (openAdj P) o r ∧
      ∀ v, ReflTransGen (openAdj P) o v → r.1.length ≤ v.1.length := by
  classical
  have hex : ∃ n : ℕ, ∃ r : TreeVertex d,
      ReflTransGen (openAdj P) o r ∧ r.1.length = n :=
    ⟨o.1.length, o, .refl, rfl⟩
  obtain ⟨r, hor, hr⟩ := Nat.find_spec hex
  refine ⟨r, hor, ?_⟩
  intro v hov
  rw [hr]
  exact Nat.find_min' hex ⟨v, hov, rfl⟩

lemma reachable_subset_downwardOpen (P : TreeVertex d → Prop) (o : TreeVertex d) :
    ∃ r, ReflTransGen (openAdj P) o r ∧
      {v | ReflTransGen (openAdj P) o v} ⊆ {v | downwardOpen P r v} := by
  obtain ⟨r, hor, hmin⟩ := exists_min_reachable P o
  refine ⟨r, hor, ?_⟩
  intro v hov
  have hrv := (reachable_symm hor).trans hov
  apply downwardOpen_of_reachable hrv
  apply prefix_of_reachable_min hrv
  intro w hrw
  exact hmin w (hor.trans hrw)

theorem finite_reachable_of_finite_downwardOpen (P : TreeVertex d → Prop)
    (h : ∀ r, {v | downwardOpen P r v}.Finite) (o : TreeVertex d) :
    {v | ReflTransGen (openAdj P) o v}.Finite := by
  obtain ⟨r, _, hsub⟩ := reachable_subset_downwardOpen P o
  exact (h r).subset hsub

lemma reachable_of_downwardOpen {P : TreeVertex d → Prop} {r v : TreeVertex d}
    (h : downwardOpen P r v) : ReflTransGen (openAdj P) r v := by
  have hwalk : ∀ n, r.1.length ≤ n → n ≤ v.1.length →
      ReflTransGen (openAdj P) r (takeVertex v n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        intro _
        have htake : takeVertex v r.1.length = r :=
          Subtype.ext (List.prefix_iff_eq_take.mp h.1).symm
        rw [htake]
    | succ n hn ih =>
        intro hnv
        have hnlt : n < v.1.length := by omega
        have hnle : n ≤ v.1.length := by omega
        refine (ih hnle).tail ⟨prefix_adj v hnlt, ?_⟩
        have hlen : (takeVertex v n).1.length < (takeVertex v (n + 1)).1.length := by
          simp only [takeVertex, List.length_take]
          rw [Nat.min_eq_left hnle, Nat.min_eq_left hnv]
          omega
        rw [ite_eq_left hlen]
        exact h.2 (n + 1) (by omega) hnv
  simpa only [prefix_length] using hwalk v.1.length h.1.length_le (le_refl _)

theorem exists_reachable_eq_downwardOpen (P : TreeVertex d → Prop)
    (o : TreeVertex d) :
    ∃ r, ReflTransGen (openAdj P) o r ∧
      {v | ReflTransGen (openAdj P) o v} = {v | downwardOpen P r v} := by
  obtain ⟨r, hor, hsub⟩ := reachable_subset_downwardOpen P o
  refine ⟨r, hor, Set.Subset.antisymm hsub ?_⟩
  intro v hv
  exact hor.trans (reachable_of_downwardOpen hv)

theorem openAdj_incoming_iff (R : TreeVertex d → TreeVertex d → Prop)
    (hsub : ∀ u v, R u v → treeAdj u v)
    (hsymm : ∀ u v, R u v → R v u) (u v : TreeVertex d) :
    openAdj (fun w => R (parentVertex w) w) u v ↔ R u v := by
  constructor
  · intro h
    by_cases hlt : u.1.length < v.1.length
    · have hp := treeAdj_parent_of_length_lt h.1 hlt
      simpa only [ite_eq_left hlt, hp] using h.2
    · have hrev : v.1.length < u.1.length := by
        obtain hl | hl := treeAdj_length h.1 <;> omega
      have hp := treeAdj_parent_of_length_lt h.1.symm hrev
      have hvu : R v u := by simpa only [ite_eq_right hlt, hp] using h.2
      exact hsymm v u hvu
  · intro h
    have hadj := hsub u v h
    refine ⟨hadj, ?_⟩
    by_cases hlt : u.1.length < v.1.length
    · have hp := treeAdj_parent_of_length_lt hadj hlt
      simpa only [ite_eq_left hlt, hp] using h
    · have hrev : v.1.length < u.1.length := by
        obtain hl | hl := treeAdj_length hadj <;> omega
      have hp := treeAdj_parent_of_length_lt hadj.symm hrev
      simpa only [ite_eq_right hlt, hp] using hsymm u v h

theorem finite_reachable_of_finite_incoming
    (R : TreeVertex d → TreeVertex d → Prop)
    (hsub : ∀ u v, R u v → treeAdj u v)
    (hsymm : ∀ u v, R u v → R v u)
    (hfinite : ∀ r, {v | downwardOpen (fun w => R (parentVertex w) w) r v}.Finite)
    (o : TreeVertex d) : {v | ReflTransGen R o v}.Finite := by
  have hR : openAdj (fun w => R (parentVertex w) w) = R := by
    funext u v
    exact propext (openAdj_incoming_iff R hsub hsymm u v)
  simpa only [hR] using
    finite_reachable_of_finite_downwardOpen (fun w => R (parentVertex w) w) hfinite o

end Problem367.OpenCluster

end

end OAI
