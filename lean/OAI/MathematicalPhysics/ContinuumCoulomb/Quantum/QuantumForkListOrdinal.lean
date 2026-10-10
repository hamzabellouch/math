import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListIndex

namespace OAI

/-! The explicit prefix index is a bijection between center-local pairs and
the consecutive mediator numbers used by the literal compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical

abbrev LocalPair (gs : Groups) := Σ i : Fin gs.length, Fin ((groupAt gs i.val).length/2)

def pairIndex (gs : Groups) (p : LocalPair gs) : Fin (pairCount gs) :=
  ⟨pairStart gs p.1.val+p.2.val,pair_index_lt gs p.1.val p.2.val p.1.isLt p.2.isLt⟩

theorem pairIndex_injective (gs : Groups) : Function.Injective (pairIndex gs) := by
  intro p q h
  have hp := catalog_getElem? gs p.1.val p.2.val p.1.isLt p.2.isLt
  have hq := catalog_getElem? gs q.1.val q.2.val q.1.isLt q.2.isLt
  have hn : pairStart gs p.1.val+p.2.val=pairStart gs q.1.val+q.2.val := congrArg Fin.val h
  rw [hn,hq] at hp
  have hc : p.1=q.1 := Fin.ext (congrArg Prod.fst (Option.some.inj hp)).symm
  rcases p with ⟨i,j⟩
  rcases q with ⟨k,l⟩
  dsimp only at hc
  subst k
  have hj : j=l := Fin.ext (by dsimp only at hn; omega)
  subst l
  rfl

theorem localPair_card (gs : Groups) : Fintype.card (LocalPair gs)=pairCount gs := by
  simp only [LocalPair,Fintype.card_sigma,Fintype.card_fin]
  have hlist : List.ofFn (fun i : Fin gs.length => (groupAt gs i.val).length/2) =
      gs.map (fun ps => ps.length/2) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hi' : i < gs.length := by simpa only [List.length_ofFn] using hi
      simp only [List.getElem_ofFn,List.getElem_map,groupAt,List.headD_eq_head?_getD,
        List.head?_drop,List.getElem?_eq_getElem hi',Option.getD_some]
  rw [← List.sum_ofFn,hlist]
  rfl

def pairEquiv (gs : Groups) : LocalPair gs ≃ Fin (pairCount gs) :=
  Equiv.ofBijective (pairIndex gs) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨pairIndex_injective gs,by rw [Fintype.card_fin,localPair_card]⟩)

theorem pairEquiv_val (gs : Groups) (p : LocalPair gs) :
    (pairEquiv gs p).val=pairStart gs p.1.val+p.2.val := rfl

theorem catalog_pairEquiv (gs : Groups) (p : LocalPair gs) :
    ((catalog gs).drop (pairEquiv gs p).val).headD (0,((0,0),(0,0))) =
      (p.1.val,(portAt (groupAt gs p.1.val) (2*p.2.val),
        portAt (groupAt gs p.1.val) (2*p.2.val+1))) :=
  catalog_headD gs p.1.val p.2.val p.1.isLt p.2.isLt

end ContinuumCoulomb.QuantumForkList

end

end OAI
