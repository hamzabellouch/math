import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingTable

namespace OAI

/-! The finite table is the data of the actual port routes. Its membership
tests agree exactly with the permissions used in the geometric proof. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open QuantumRoutingTable
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def routingVisits : List Visit :=
  (Finset.univ : Finset P.Interior).toList.flatMap (fun i =>
    [(P.cell i,((P.port i 0).val,(P.port i 1).val)),
     (P.cell i,((P.port i 1).val,(P.port i 0).val))])

def routingTable : Table :=
  (List.ofFn P.position,P.routingVisits,P.crossingCells.toList)

theorem routingTable_source (p : ℕ × ℕ) :
    p ∈ P.routingTable.1 ↔ ∃ v, P.position v = p := by
  exact List.mem_ofFn

theorem routingTable_crossing (p : ℕ × ℕ) :
    p ∈ P.routingTable.2.2 ↔ P.IsCrossing p := by
  exact Finset.mem_toList.trans P.mem_crossingCells

theorem routingTable_pair (p : ℕ × ℕ) (a b : Fin 4) :
    (p,(a.val,b.val)) ∈ P.routingTable.2.1 ↔
      ∃ i : P.Interior, P.cell i = p ∧ s(P.port i 0,P.port i 1) = s(a,b) := by
  change (p,(a.val,b.val)) ∈ P.routingVisits ↔ _
  simp only [routingVisits,List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,
    List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq,Sym2.eq_iff]
  constructor
  · rintro ⟨i,⟨hc,ha,hb⟩ | ⟨hc,ha,hb⟩⟩
    · exact ⟨i,hc.symm,Or.inl ⟨(Fin.ext ha).symm,(Fin.ext hb).symm⟩⟩
    · exact ⟨i,hc.symm,Or.inr ⟨(Fin.ext hb).symm,(Fin.ext ha).symm⟩⟩
  · rintro ⟨i,hc,⟨ha,hb⟩ | ⟨ha,hb⟩⟩
    · exact ⟨i,Or.inl ⟨hc.symm,congrArg Fin.val ha.symm,congrArg Fin.val hb.symm⟩⟩
    · exact ⟨i,Or.inr ⟨hc.symm,congrArg Fin.val hb.symm,congrArg Fin.val ha.symm⟩⟩

theorem routingTable_allowed (R : QMACellRouteBody) :
    allowed P.routingTable R = true ↔ P.RoutingAllowed R := by
  cases R with
  | ray p a =>
    simp only [allowed,Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_true_eq,
      decide_eq_false_iff_not,routingTable_source,routingTable_crossing,RoutingAllowed]
  | pair p e =>
    simp only [allowed,Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_true_eq,
      decide_eq_false_iff_not,routingTable_pair,routingTable_crossing,RoutingAllowed]
  | patch p e =>
    simp only [allowed,decide_eq_true_eq,routingTable_crossing,RoutingAllowed]
  | corridor p a b c =>
    have h (q : ℕ × ℕ) : decide (q ∈ P.routingTable.2.2) = decide (P.IsCrossing q) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,P.routingTable_crossing]
    simp only [allowed,Bool.and_eq_true,decide_eq_true_eq,h,RoutingAllowed]

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
