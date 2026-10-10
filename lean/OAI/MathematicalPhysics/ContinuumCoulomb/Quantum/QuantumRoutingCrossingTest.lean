import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingTableCorrectness

namespace OAI

/-! Crossing cells are detected from the two opposite port pairs in the finite
visit table. No search over a proof-level finite type is needed. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingTable
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

 theorem crossing_iff_opposite_visits (p : Pair) : P.IsCrossing p ↔
    (p,(0,2)) ∈ P.routingTable.2.1 ∧ (p,(1,3)) ∈ P.routingTable.2.1 := by
  have h02 := P.routingTable_pair p (0 : Fin 4) 2
  have h13 := P.routingTable_pair p (1 : Fin 4) 3
  change ((p,(0,2)) ∈ P.routingTable.2.1 ↔ _) at h02
  change ((p,(1,3)) ∈ P.routingTable.2.1 ↔ _) at h13
  rw [h02,h13]
  constructor
  · rintro ⟨i,j,hij,hi,hj,hpair⟩
    have h02 : s(0,2) ∈ P.pairing i j := by
      rw [hpair]
      simp [qmaCrossPortPairing]
    have h13 : s(1,3) ∈ P.pairing i j := by
      rw [hpair]
      simp [qmaCrossPortPairing]
    change s(0,2) ∈ ({s(P.port i 0,P.port i 1),s(P.port j 0,P.port j 1)} :
      Finset (Sym2 (Fin 4))) at h02
    change s(1,3) ∈ ({s(P.port i 0,P.port i 1),s(P.port j 0,P.port j 1)} :
      Finset (Sym2 (Fin 4))) at h13
    simp only [Finset.mem_insert,Finset.mem_singleton] at h02 h13
    rcases h02 with h02 | h02
    · refine ⟨⟨i,hi,h02.symm⟩,?_⟩
      rcases h13 with h13 | h13
      · exact False.elim ((by decide : (s(0,2) : Sym2 (Fin 4)) ≠ s(1,3))
          (h02.trans h13.symm))
      · exact ⟨j,hj,h13.symm⟩
    · refine ⟨⟨j,hj,h02.symm⟩,?_⟩
      rcases h13 with h13 | h13
      · exact ⟨i,hi,h13.symm⟩
      · exact False.elim ((by decide : (s(0,2) : Sym2 (Fin 4)) ≠ s(1,3))
          (h02.trans h13.symm))
  · rintro ⟨⟨i,hi,h02⟩,⟨j,hj,h13⟩⟩
    have hij : i ≠ j := by
      intro he
      subst j
      exact (by decide : (s(0,2) : Sym2 (Fin 4)) ≠ s(1,3)) (h02.symm.trans h13)
    refine ⟨i,j,hij,hi,hj,?_⟩
    change {s(P.port i 0,P.port i 1),s(P.port j 0,P.port j 1)} = _
    rw [h02,h13]
    rfl

end QMAPortRouteData
namespace QuantumRoutingTable

def crossingTest (t : Table) (p : Pair) : Bool :=
  decide ((p,(0,2)) ∈ t.2.1) && decide ((p,(1,3)) ∈ t.2.1)

def computedCrossings (t : Table) : List Pair :=
  (t.2.1.map Prod.fst).filter (crossingTest t)

 theorem mem_computedCrossings (t : Table) (p : Pair) :
    p ∈ computedCrossings t ↔ crossingTest t p = true := by
  simp only [computedCrossings,List.mem_filter]
  constructor
  · exact And.right
  · intro h
    have hv : (p,(0,2)) ∈ t.2.1 := by
      have hh : decide ((p,(0,2)) ∈ t.2.1) = true ∧
          decide ((p,(1,3)) ∈ t.2.1) = true := by
        simpa only [crossingTest,Bool.and_eq_true] using h
      exact of_decide_eq_true hh.1
    exact ⟨List.mem_map.mpr ⟨(p,(0,2)),hv,rfl⟩,h⟩

 theorem crossingTest_correct {G : QMARationalExchangeGraph} (P : QMAPortRouteData G) (p : Pair) :
    crossingTest P.routingTable p = true ↔ P.IsCrossing p := by
  simp only [crossingTest,Bool.and_eq_true,decide_eq_true_eq]
  exact (P.crossing_iff_opposite_visits p).symm

 theorem computedCrossings_correct {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (p : Pair) : p ∈ computedCrossings P.routingTable ↔ P.IsCrossing p := by
  rw [mem_computedCrossings,crossingTest_correct]

noncomputable def crossingTestProgram : Procedure inputCode Procedure.boolCode
    (fun x => crossingTest x.1 x.2) := by
  let memp := QuantumFiniteMembership.memberProgram visitCode ((0,0),(0,0))
    (Procedure.prodEq QuantumFiniteMembership.pairEqProgram QuantumFiniteMembership.pairEqProgram)
  let check (a b : ℕ) := memp.comp
    ((cellProgram.pair (Procedure.constant inputCode pairCode (a,b))).pair visitsProgram)
  exact Procedure.boolAnd.comp ((check 0 2).pair (check 1 3))

end QuantumRoutingTable
end ContinuumCoulomb

end

end OAI
