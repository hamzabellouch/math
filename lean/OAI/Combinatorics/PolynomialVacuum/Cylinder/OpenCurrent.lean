import OAI.Combinatorics.PolynomialVacuum.Cylinder.OpenWord
import OAI.Combinatorics.PolynomialVacuum.Cylinder.OpenIce

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

 

noncomputable def arcFlow (g : Germ M) (w : List Bool) : Edge M →₀ ℤ :=
  wordFlow g w - dartFlow g

theorem orientedFlow_arc (g : Germ M) (w : List Bool) :
    orientedFlow (arcFlow g w)=turnVisit g w + Finsupp.single (reverseGerm g) 1 -
      Finsupp.single (terminalGerm g w) 1 := by
  rw [arcFlow,map_sub,orientedFlow_wordFlow,orientedFlow_dartFlow]
  abel

theorem turnVisit_array {n : ℕ} (g : Fin (n+1) → Germ M) (b : Fin n → Bool)
    (h : ∀ i : Fin n,advance (g i.castSucc) (b i)=g i.succ) :
    turnVisit (g 0) (List.ofFn b)=∑ i : Fin n,
      (Finsupp.single ((g i.castSucc).1,outgoingSlot (g i.castSucc) (b i)) 1 -
        Finsupp.single (g i.castSucc) 1) := by
  induction n with
  | zero => simp [turnVisit]
  | succ n ih =>
    have ht : ∀ i : Fin n,advance (Fin.tail g i.castSucc) (Fin.tail b i)=Fin.tail g i.succ := by
      intro i
      exact h i.succ
    have hh:=ih (Fin.tail g) (Fin.tail b) ht
    simp only [Fin.tail] at hh
    have h0 : advance (g 0) (b 0)=g (Fin.succ 0) := h 0
    have hh' : turnVisit (g (Fin.succ 0)) (List.ofFn (fun i : Fin n => b i.succ)) =
        ∑ i : Fin n,(Finsupp.single ((g i.castSucc.succ).1,
          outgoingSlot (g i.castSucc.succ) (b i.succ)) 1 - Finsupp.single (g i.castSucc.succ) 1) := hh
    rw [List.ofFn_succ,turnVisit,h0,hh',Fin.sum_univ_succ]
    rfl

namespace OpenNetwork
variable (C : OpenNetwork M)

theorem pathWord_turnVisit (a : C.sites) (ha : C.Source a) :
    turnVisit (a.val,C.enter a) (C.pathWord a ha)=∑ j : Fin (C.pathLength a ha),
      (Finsupp.single ((C.pathSite a ha j).val,C.exit (C.pathSite a ha j)) 1 -
        Finsupp.single ((C.pathSite a ha j).val,C.enter (C.pathSite a ha j)) 1) := by
  have h:=turnVisit_array (C.pathGerm a ha) (fun j => C.turn (C.pathSite a ha j))
    (C.pathGerm_step a ha)
  simpa only [C.pathGerm_start,C.pathGerm_cast,C.outgoing_turn,pathWord] using h

theorem pathWord_turn_at (a : C.sites) (ha : C.Source a)
    (j : Fin (C.pathLength a ha)) (k : Fin 3) :
    turnVisit (a.val,C.enter a) (C.pathWord a ha) ((C.pathSite a ha j).val,k)=
      (if k=C.exit (C.pathSite a ha j) then 1 else 0)-
        (if k=C.enter (C.pathSite a ha j) then 1 else 0) := by
  rw [C.pathWord_turnVisit,Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single j]
  · simp [Finsupp.single_apply,eq_comm]
  · intro i _ hij
    have hn : (C.pathSite a ha i).val≠(C.pathSite a ha j).val := by
      intro hh
      exact hij (C.pathSite_injective a ha (Subtype.ext hh))
    simp [hn]
  · simp
end OpenNetwork

namespace OpenIce
variable (D : Finset (Vertex M)) (q : Edge M →₀ ℤ) (hq : ∀v∈D,LocalIce q v)

noncomputable def extractedArc (a : activeInside D q) (ha : (network D q hq).Source a) :
    Edge M →₀ ℤ := arcFlow (a.val,enter D q hq a) ((network D q hq).pathWord a ha)

theorem arc_on_domain (a : activeInside D q) (ha : (network D q hq).Source a)
    (v : Vertex M) (hv : v∈D) (k : Fin 3) :
    orientedFlow (extractedArc D q hq a ha) (v,k)=
      turnVisit (a.val,enter D q hq a) ((network D q hq).pathWord a ha) (v,k) := by
  have hs : neighbor a.val (enter D q hq a)∉D := enter_outside_domain D q hq a ha
  have he : ((network D q hq).pathEnd a ha).1∉D := by
    apply exit_outside_domain D q hq
    apply (network D q hq).pathSite_exit a ha ((network D q hq).pathLast a ha)
    change (network D q hq).pathLength a ha-1+1=(network D q hq).pathLength a ha
    have := (network D q hq).pathLength_pos a ha
    omega
  have hs' : reverseGerm (a.val,enter D q hq a)≠(v,k) := by
    intro hh
    apply hs
    have hvv:=congrArg Prod.fst hh
    change neighbor a.val (enter D q hq a)=v at hvv
    rw [hvv]
    exact hv
  have he' : terminalGerm (a.val,enter D q hq a) ((network D q hq).pathWord a ha)≠(v,k) := by
    have ht : terminalGerm (a.val,enter D q hq a) ((network D q hq).pathWord a ha)=
        (network D q hq).pathEnd a ha := (network D q hq).pathWord_terminal a ha
    rw [ht]
    intro hh
    exact he ((congrArg Prod.fst hh).symm ▸ hv)
  rw [extractedArc,orientedFlow_arc]
  simp [hs',he']

 

theorem remove_arc_ice (a : activeInside D q) (ha : (network D q hq).Source a) :
    ∀v∈D,LocalIce (q-extractedArc D q hq a ha) v := by
  intro v hv
  by_cases hp : v∈traced (a.val,enter D q hq a) ((network D q hq).pathWord a ha)
  · left
    have ht : traced (a.val,enter D q hq a) ((network D q hq).pathWord a ha)=
        List.ofFn (fun j => ((network D q hq).pathSite a ha j).val) :=
      (network D q hq).pathWord_trace a ha
    rw [ht,List.mem_ofFn] at hp
    obtain ⟨j,rfl⟩:=hp
    intro k
    rw [map_sub,Finsupp.sub_apply,arc_on_domain D q hq a ha _ hv]
    have ht' := (network D q hq).pathWord_turn_at a ha j k
    change turnVisit (a.val,enter D q hq a) ((network D q hq).pathWord a ha)
        (((network D q hq).pathSite a ha j).val,k)=_ at ht'
    have hs := at_slot D q hq ((network D q hq).pathSite a ha j) k
    rw [ht',hs]
    exact sub_self _
  · have hz : ∀k,orientedFlow (extractedArc D q hq a ha) (v,k)=0 := by
      intro k
      rw [arc_on_domain D q hq a ha v hv]
      exact turnVisit_eq_zero_of_not_mem _ _ _ k hp
    rcases hq v hv with hempty | ⟨i,o,hio,hslots⟩
    · left
      intro k
      simp [hempty k,hz k]
    · right
      refine ⟨i,o,hio,?_⟩
      intro k
      simp [hslots k,hz k]
end OpenIce
end PolynomialVacuumCylinder

end OAI
