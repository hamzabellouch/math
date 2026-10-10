import OAI.Combinatorics.ContingencyTables.Rooted.RootedCompletion
import OAI.Combinatorics.ContingencyTables.Transport.GraphCompletionCounts

namespace OAI

/-! # The explicit endpoint on the side away from a selected root

One reachability test in the edge-deleted forest selects the endpoint.
No choice of a component representative or of a cut vertex is needed.
-/

namespace ContingencyTables.RootedCut

open scoped BigOperators Classical
open SimpleGraph MaximumForest RootedCompletion GraphCompletionCounts ForestCut
open ForestCapacity

variable {V : Type*}

noncomputable def away (T : SimpleGraph V) (u v root : V) : V :=
  if (T.deleteEdges {s(u,v)}).Reachable u root then v else u

noncomputable def cut (T : SimpleGraph V) (u v root a : V) : Bool :=
  side (T.deleteEdges {s(u,v)}) (away T u v root) a

theorem away_properties (T : SimpleGraph V) (hT : T.IsAcyclic) {u v : V}
    (ht : T.Adj u v) (root : V) (hr : T.Reachable root u) :
    T.Reachable root (away T u v root) ∧ cut T u v root root=false ∧
      cut T u v root u≠cut T u v root v := by
  let D := T.deleteEdges {s(u,v)}
  have hsep : ¬D.Reachable u v :=
    isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT ht)
  by_cases hru : D.Reachable u root
  · have ha : away T u v root=v := ite_eq_left hru
    refine ⟨by simpa only [ha] using hr.trans ht.reachable,?_,?_⟩
    · have hn : ¬D.Reachable v root := fun h => hsep (hru.trans h.symm)
      change side D (away T u v root) root=false
      rw [ha]
      simpa only [side,decide_eq_false_iff_not] using hn
    · have hn : ¬D.Reachable v u := fun h => hsep h.symm
      change side D (away T u v root) u≠side D (away T u v root) v
      rw [ha]
      simp [side,hn]
  · have ha : away T u v root=u := ite_eq_right hru
    refine ⟨by simpa only [ha] using hr,?_,?_⟩
    · change side D (away T u v root) root=false
      rw [ha]
      simpa only [side,decide_eq_false_iff_not] using hru
    · change side D (away T u v root) u≠side D (away T u v root) v
      rw [ha]
      simp [side,hsep]

theorem selected_nonroot (T : SimpleGraph V) (S : Selection T) (hT : T.IsAcyclic)
    {u v a : V} (ht : T.Adj u v) (ha : cut T u v (S.root u) a=true) : a≠S.root a := by
  intro he
  have hp := away_properties T hT ht (S.root u) (S.reachable u).symm
  have hreach : (T.deleteEdges {s(u,v)}).Reachable (away T u v (S.root u)) a := by
    simpa only [cut,side,decide_eq_true_eq] using ha
  have hcomp := hp.1.trans (hreach.mono (T.deleteEdges_le {s(u,v)}))
  have hsame : S.root a=S.root u :=
    (S.constant hcomp).symm.trans (S.idempotent u)
  have hae : a=S.root u := he.trans hsame
  have hbad : cut T u v (S.root u) (S.root u)=true := by simpa only [hae] using ha
  exact Bool.false_ne_true (hp.2.1.symm.trans hbad)

variable {I J : Type*}

noncomputable def treeCut (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (v : I⊕J) : Bool :=
  cut T (.inl t.val.1) (.inr t.val.2) (S.root (.inl t.val.1)) v

lemma treeCut_self (T : SimpleGraph (I⊕J)) (S : Selection T) (hT : T.IsAcyclic)
    (t : TreeCell T) : treeCut T S t (.inl t.val.1)≠treeCut T S t (.inr t.val.2) :=
  (away_properties T hT t.property _ (S.reachable _).symm).2.2

lemma treeCut_nonroot (T : SimpleGraph (I⊕J)) (S : Selection T) (hT : T.IsAcyclic)
    (t : TreeCell T) (v : I⊕J) (hv : treeCut T S t v=true) : v≠S.root v :=
  selected_nonroot T S hT t.property hv

noncomputable def sign (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (a : I×J) : ℝ :=
  indicator (treeCut T S t (.inl a.1))-indicator (treeCut T S t (.inr a.2))

lemma sign_abs_self (T : SimpleGraph (I⊕J)) (S : Selection T) (hT : T.IsAcyclic)
    (t : TreeCell T) : |sign T S t t.val|=1 :=
  abs_indicator_sub (treeCut_self T S hT t)

lemma sign_self_ne_zero (T : SimpleGraph (I⊕J)) (S : Selection T) (hT : T.IsAcyclic)
    (t : TreeCell T) : sign T S t t.val≠0 := by
  intro hz
  have hh := sign_abs_self T S hT t
  rw [hz,abs_zero] at hh
  norm_num at hh

lemma sign_abs_le_one (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (a : I×J) : |sign T S t a|≤1 := by
  unfold sign
  cases treeCut T S t (.inl a.1) <;> cases treeCut T S t (.inr a.2) <;>
    norm_num [indicator]

lemma other_tree_sign_zero (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (a : I×J) (ha : T.Adj (.inl a.1) (.inr a.2)) (hne : a≠t.val) :
    sign T S t a=0 := by
  have hh := side_eq_of_tree_edge T (s(Sum.inl t.val.1,Sum.inr t.val.2))
    (away T (.inl t.val.1) (.inr t.val.2) (S.root (.inl t.val.1))) ha
    (by intro he; exact hne (cell_edge_injective he))
  exact sub_eq_zero.mpr (congrArg indicator hh)

end ContingencyTables.RootedCut

end OAI
