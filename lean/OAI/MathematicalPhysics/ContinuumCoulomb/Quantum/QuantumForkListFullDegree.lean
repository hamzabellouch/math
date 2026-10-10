import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListDegreeIteration
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkStateDegree

namespace OAI

/-! The complete literal exchange list has degree at most three once each
active group has at most three ports. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

abbrev PortIndex (gs : Groups) := Σ i : Fin gs.length, Fin (groupAt gs i.val).length

def portSite {n : ℕ} {gs : Groups} (h : ValidPorts n gs) (p : PortIndex gs) : Fin n :=
  ⟨(portAt (groupAt gs p.1.val) p.2.val).1,h.bounded p.1 p.2⟩

theorem portSite_injective {n : ℕ} {gs : Groups} (h : ValidPorts n gs) :
    Function.Injective (portSite h) := by
  intro p q hpq
  have he := h.injective p.1 q.1 p.2 q.2 (congrArg Fin.val hpq)
  apply Sigma.ext he.1
  exact (Fin.heq_ext_iff (congrArg (fun i : Fin gs.length => (groupAt gs i.val).length) he.1)).2 he.2

def asForkPorts {n : ℕ} {gs : Groups} (h : ValidPorts n gs) :
    QMAForkPorts n gs.length (fun i => (groupAt gs i.val).length) where
  center i := ⟨i.val,lt_of_lt_of_le i.isLt h.centers⟩
  port := portSite h
  center_injective := by
    intro i j he
    exact Fin.ext (congrArg (fun v : Fin n => v.val) he)
  port_injective := portSite_injective h
  center_ne_port := fun i p he => h.disjoint i p.1 p.2 (congrArg Fin.val he)

def asForkState (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1)
    (hn : ∀ b ∈ s.2.1, b.1 ≠ b.2.1) (hd : DegreeBounds s) :
    QMAForkState s.1 s.2.2.2.length (fun i => (groupAt s.2.2.2 i.val).length)
      (Fin s.2.1.length) where
  ports := asForkPorts hs
  left := (SourceBondLists.bonds s.1 s.2.1 hb).left
  right := (SourceBondLists.bonds s.1 s.2.1 hb).right
  distinct e := fun he => hn (s.2.1.get e) (List.get_mem _ e) (congrArg Fin.val he)
  degree_le := fun v => (degree_eq_graph s.1 s.2.1 hb v) ▸ hd.ordinary v
  center_degree := by
    intro i
    rw [← degree_eq_graph]
    exact hd.center i.val i.isLt
  port_degree := by
    intro p
    rw [← degree_eq_graph]
    exact hd.port p.1 p.2

theorem active_index_sum {M : Type*} [AddCommMonoid M] (gs : Groups) (f : Bond → M) :
    ((activeBonds gs).map f).sum =
      ∑ p : PortIndex gs, f (p.1.val,(portAt (groupAt gs p.1.val) p.2.val).1,
        (portAt (groupAt gs p.1.val) p.2.val).2) := by
  simp only [activeBonds,starBonds,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def,range_sum,PortIndex,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  have hp (j : Fin (groupAt gs i.val).length) :
      portAt (groupAt gs i.val) j.val=(groupAt gs i.val).get j := by
    simpa only [List.get_eq_getElem] using portAt_eq_getElem _ _ j.isLt
  simp only [hp]
  rw [← List.sum_ofFn]
  simpa only [List.get_eq_getElem] using congrArg List.sum
    (List.ofFn_getElem_eq_map (groupAt gs i.val) (fun p => f (i.val,p.1,p.2))).symm

theorem full_degree_eq (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1)
    (hn : ∀ b ∈ s.2.1, b.1 ≠ b.2.1) (hd : DegreeBounds s) (v : Fin s.1) :
    degree (s.2.1++activeBonds s.2.2.2) v.val =
      qmaGraphDegree (asForkState s hs hb hn hd).fullLeft
        (asForkState s hs hb hn hd).fullRight v := by
  rw [degree_append]
  rw [graph_degree_incident]
  simp only [degree,active_index_sum,QMAForkState.fullLeft,QMAForkState.fullRight,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    asForkState,asForkPorts,portSite,SourceBondLists.bonds]
  rw [initial_list_sum]

theorem full_degree_le_three (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1)
    (hn : ∀ b ∈ s.2.1, b.1 ≠ b.2.1) (hd : DegreeBounds s)
    (hl : ∀ i : Fin s.2.2.2.length, (groupAt s.2.2.2 i.val).length ≤ 3) (v : Fin s.1) :
    degree (s.2.1++activeBonds s.2.2.2) v.val ≤ 3 := by
  rw [full_degree_eq s hs hb hn hd]
  exact (asForkState s hs hb hn hd).full_degree_le_three hl v

end ContinuumCoulomb.QuantumForkList

end

end OAI
