import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathVisitProgram

namespace OAI

/-! The encoded consecutive-point rule recovers the actual directional ports
of every interior visit in the proved port-route geometry. -/

noncomputable section
namespace ContinuumCoulomb
open QuantumRouteCode QuantumRoutingTable QuantumPathVisitProgram

namespace QuantumPathVisitProgram
 theorem lookup_range (f : ℕ → Pair) (n i : ℕ) (hi : i < n) :
    lookup ((List.range n).map f) i = f i := by
  simp only [lookup,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_map,
    List.getElem?_range hi,Option.map_some,Option.getD_some]

 theorem both_member (p c : Pair) (a b u v : Fin 4) :
    (p,(a.val,b.val)) ∈ both (c,(u.val,v.val)) ↔ c=p ∧ s(u,v)=s(a,b) := by
  simp only [both,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq,
    Prod.swap_prod_mk,Sym2.eq_iff]
  constructor
  · rintro (⟨hc,ha,hb⟩ | ⟨hc,ha,hb⟩)
    · exact ⟨hc.symm,Or.inl ⟨(Fin.ext ha).symm,(Fin.ext hb).symm⟩⟩
    · exact ⟨hc.symm,Or.inr ⟨(Fin.ext hb).symm,(Fin.ext ha).symm⟩⟩
  · rintro ⟨hc,⟨ha,hb⟩ | ⟨ha,hb⟩⟩
    · exact Or.inl ⟨hc.symm,congrArg Fin.val ha.symm,congrArg Fin.val hb.symm⟩
    · exact Or.inr ⟨hc.symm,congrArg Fin.val hb.symm,congrArg Fin.val ha.symm⟩
end QuantumPathVisitProgram

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def routeList (e : G.Edge) : List Pair :=
  (List.range (P.length e+1)).map (P.point e)

 theorem routeList_lookup (e : G.Edge) (i : ℕ) (hi : i ≤ P.length e) :
    lookup (P.routeList e) i = P.point e i :=
  QuantumPathVisitProgram.lookup_range _ _ _ (by omega)

 theorem routeList_visit (e : G.Edge) (j : Fin (P.length e-1)) :
    visit (P.routeList e) j.val =
      (P.cell ⟨e,j⟩,((P.port ⟨e,j⟩ 0).val,(P.port ⟨e,j⟩ 1).val)) := by
  have hj := j.isLt
  simp only [visit,P.routeList_lookup e j.val (by omega),
    P.routeList_lookup e (j.val+1) (by omega),P.routeList_lookup e (j.val+2) (by omega),
    cell,port,arm,armIndex,Fin.val_zero,Fin.val_one,mul_zero,mul_one,Nat.add_zero]

 theorem routeList_visits (e : G.Edge) (p : Pair) (a b : Fin 4) :
    (p,(a.val,b.val)) ∈ visits (P.routeList e) ↔
      ∃ j : Fin (P.length e-1), P.cell ⟨e,j⟩ = p ∧
        s(P.port ⟨e,j⟩ 0,P.port ⟨e,j⟩ 1) = s(a,b) := by
  have hlen : (P.routeList e).length-2 = P.length e-1 := by
    simp only [routeList,List.length_map,List.length_range]
    omega
  rw [visits,← List.flatMap_def,hlen,List.mem_flatMap]
  constructor
  · rintro ⟨j,hj,hv⟩
    have hj' : j < P.length e-1 := List.mem_range.mp hj
    rw [P.routeList_visit e ⟨j,hj'⟩] at hv
    exact ⟨⟨j,hj'⟩,(QuantumPathVisitProgram.both_member _ _ _ _ _ _).mp hv⟩
  · rintro ⟨j,hj⟩
    refine ⟨j.val,List.mem_range.mpr j.isLt,?_⟩
    rw [P.routeList_visit e j]
    exact (QuantumPathVisitProgram.both_member _ _ _ _ _ _).mpr hj

 theorem routeList_visits_general (e : G.Edge) (v : Visit) :
    v ∈ visits (P.routeList e) ↔
      ∃ j : Fin (P.length e-1),
        v ∈ both (P.cell ⟨e,j⟩,((P.port ⟨e,j⟩ 0).val,(P.port ⟨e,j⟩ 1).val)) := by
  have hlen : (P.routeList e).length-2 = P.length e-1 := by
    simp only [routeList,List.length_map,List.length_range]
    omega
  rw [visits,← List.flatMap_def,hlen,List.mem_flatMap]
  constructor
  · rintro ⟨j,hj,hv⟩
    have hj' : j < P.length e-1 := List.mem_range.mp hj
    rw [P.routeList_visit e ⟨j,hj'⟩] at hv
    exact ⟨⟨j,hj'⟩,hv⟩
  · rintro ⟨j,hj⟩
    refine ⟨j.val,List.mem_range.mpr j.isLt,?_⟩
    rw [P.routeList_visit e j]
    exact hj

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
