import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellPathTemplates
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPairSupport

namespace OAI

/-! The actual two-port visits choose compatible ordinary-cell paths. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def cellPairIndex (i : P.Interior) : Fin 6 :=
  Classical.choose (qmaCellPair_complete (P.port i 0) (P.port i 1)
    ((P.port_injective i).ne (by decide)))

theorem cellPairIndex_spec (i : P.Interior) :
    (P.port i 0 = qmaCellPairLeft (P.cellPairIndex i) ∧
     P.port i 1 = qmaCellPairRight (P.cellPairIndex i)) ∨
    (P.port i 0 = qmaCellPairRight (P.cellPairIndex i) ∧
     P.port i 1 = qmaCellPairLeft (P.cellPairIndex i)) :=
  Classical.choose_spec (qmaCellPair_complete (P.port i 0) (P.port i 1)
    ((P.port_injective i).ne (by decide)))

theorem cellPairIndex_pair (i : P.Interior) :
    s(qmaCellPairLeft (P.cellPairIndex i),qmaCellPairRight (P.cellPairIndex i)) =
      s(P.port i 0,P.port i 1) := by
  rcases P.cellPairIndex_spec i with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [ha,hb]
  · rw [ha,hb]
    exact Sym2.eq_swap

theorem cellPairIndex_left (i : P.Interior) :
    qmaCellPairLeft (P.cellPairIndex i) = P.port i 0 ∨
      qmaCellPairLeft (P.cellPairIndex i) = P.port i 1 := by
  rcases P.cellPairIndex_spec i with h | h
  · exact Or.inl h.1.symm
  · exact Or.inr h.2.symm

theorem cellPairIndex_right (i : P.Interior) :
    qmaCellPairRight (P.cellPairIndex i) = P.port i 0 ∨
      qmaCellPairRight (P.cellPairIndex i) = P.port i 1 := by
  rcases P.cellPairIndex_spec i with h | h
  · exact Or.inr h.2.symm
  · exact Or.inl h.1.symm

theorem cellPairIndex_non_cross {i j : P.Interior} (hij : i ≠ j)
    (hc : P.cell i = P.cell j) (hn : ¬P.IsCrossing (P.cell i)) :
    ¬(P.cellPairIndex i = 1 ∧ P.cellPairIndex j = 4) ∧
    ¬(P.cellPairIndex i = 4 ∧ P.cellPairIndex j = 1) := by
  have hp : P.pairing i j =
      {s(qmaCellPairLeft (P.cellPairIndex i),qmaCellPairRight (P.cellPairIndex i)),
       s(qmaCellPairLeft (P.cellPairIndex j),qmaCellPairRight (P.cellPairIndex j))} := by
    rw [P.cellPairIndex_pair,P.cellPairIndex_pair]
    rfl
  constructor
  · rintro ⟨hi,hj⟩
    apply hn
    refine ⟨i,j,hij,rfl,hc.symm,?_⟩
    rw [hp,hi,hj]
    rfl
  · rintro ⟨hi,hj⟩
    apply hn
    refine ⟨i,j,hij,rfl,hc.symm,?_⟩
    rw [hp,hi,hj]
    change {s(1,3),s(0,2)} = {s(0,2),s(1,3)}
    exact Finset.pair_comm _ _

theorem ordinary_visit_paths_disjoint {i j : P.Interior} (hij : i ≠ j)
    (hc : P.cell i = P.cell j) (hn : ¬P.IsCrossing (P.cell i)) :
    Disjoint (qmaCellPairPath (P.cellPairIndex i)).toFinset
      (qmaCellPairPath (P.cellPairIndex j)).toFinset := by
  have hne (x y : Fin 4) (hx : x = P.port i 0 ∨ x = P.port i 1)
      (hy : y = P.port j 0 ∨ y = P.port j 1) : x ≠ y := by
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals exact P.different_visits_ports hij hc _ _
  exact qmaCellPair_disjoint _ _
    (hne _ _ (P.cellPairIndex_left i) (P.cellPairIndex_left j))
    (hne _ _ (P.cellPairIndex_left i) (P.cellPairIndex_right j))
    (hne _ _ (P.cellPairIndex_right i) (P.cellPairIndex_left j))
    (hne _ _ (P.cellPairIndex_right i) (P.cellPairIndex_right j))
    (P.cellPairIndex_non_cross hij hc hn)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
