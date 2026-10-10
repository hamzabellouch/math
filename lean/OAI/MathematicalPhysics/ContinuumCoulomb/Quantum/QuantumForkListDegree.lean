import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialCalibration
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkBackground

namespace OAI

/-! Incidence counts for the literal ordinary-bond list. The four newly emitted
bonds have exactly the graph used by the physical fork degree estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph MediatorListProgram
open scoped BigOperators Classical

def incident (v a b : ℕ) : ℕ := if a=v ∨ b=v then 1 else 0

def degree (bs : List Bond) (v : ℕ) : ℕ :=
  (bs.map (fun b => incident v b.1 b.2.1)).sum

theorem graph_degree_incident {ν : Type*} [Fintype ν] {n : ℕ}
    (left right : ν → Fin n) (v : Fin n) :
    qmaGraphDegree left right v=∑ e, incident v.val (left e).val (right e).val := by
  unfold qmaGraphDegree
  apply Finset.sum_congr rfl
  intro e _
  simp only [incident,Fin.ext_iff]

theorem degree_append (bs cs : List Bond) (v : ℕ) :
    degree (bs++cs) v=degree bs v+degree cs v := by
  simp only [degree,List.map_append,List.sum_append]

theorem degree_eq_graph (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (v : Fin n) :
    degree bs v.val=qmaGraphDegree (SourceBondLists.bonds n bs hb).left
      (SourceBondLists.bonds n bs hb).right v := by
  unfold degree
  rw [initial_list_sum]
  rw [graph_degree_incident]
  rfl

theorem added_sum {M : Type*} [AddCommMonoid M] (s : State)
    (hs : ValidPorts s.1 s.2.2.2) (R : ℚ) (f : Bond → M) :
    ((addedBonds s R).map f).sum = ∑ e : Fin (pairCount s.2.2.2),
      (f ((actualSite hs e 1).val,(actualSite hs e 2).val,
          2*actualJ s.2.2.2 e*actualK s.2.2.2 e)+
       f (s.1+2*e.val,s.1+2*e.val+1,R^2)+
       f ((actualSite hs e 1).val,s.1+2*e.val+1,2*R*actualJ s.2.2.2 e)+
       f ((actualSite hs e 2).val,s.1+2*e.val+1,2*R*actualK s.2.2.2 e)) := by
  simp only [addedBonds,List.map_flatten,List.sum_flatten,List.map_map,Function.comp_def,
    catalog_length,range_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [catalog_actualSite hs e]
  simp only [pairBonds,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  ac_rfl

theorem next_ordinary_degree (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1)
    (v : Fin (s.1+pairCount s.2.2.2*2)) :
    degree (next N s).2.1 v.val =
      qmaGraphDegree
        (qmaForkBackgroundLeft (SourceBondLists.bonds s.1 s.2.1 hb).left (actualSite hs))
        (qmaForkBackgroundRight (SourceBondLists.bonds s.1 s.2.1 hb).right (actualSite hs)) v := by
  change degree (s.2.1++addedBonds s (scale N s)) v.val=_
  rw [degree_append]
  unfold degree
  rw [initial_list_sum,added_sum s hs]
  rw [graph_degree_incident]
  simp only [qmaForkBackgroundLeft,qmaForkBackgroundRight,
    Fintype.sum_sum_type,Fintype.sum_prod_type,qmaParallelGraphLeft,qmaParallelGraphRight,
    qmaForksBaseLeft,qmaForksBaseRight,Sum.elim_inl,Sum.elim_inr,
    qmaForkOuter,Fin.sum_univ_two,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false,
    SourceBondLists.bonds,MediatorIteration.old_val,MediatorIteration.fresh_val,
    Fin.val_zero,Fin.val_one,Nat.add_zero,Finset.sum_add_distrib]
  simp only [Nat.mul_comm]
  omega

structure DegreeBounds (s : State) : Prop where
  ordinary : ∀ v : Fin s.1, degree s.2.1 v.val ≤ 3
  center : ∀ i, i < s.2.2.2.length → degree s.2.1 i=0
  port : ∀ (i : Fin s.2.2.2.length) (j : Fin (groupAt s.2.2.2 i.val).length),
    degree s.2.1 (portAt (groupAt s.2.2.2 i.val) j.val).1 ≤ 1

end ContinuumCoulomb.QuantumForkList

end

end OAI
