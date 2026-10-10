import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellMatching

namespace OAI

/-! An exact finite set of crossing cells, selected from the route visits. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def pairing (i j : P.Interior) : Finset (Sym2 (Fin 4)) :=
  qmaPortPairing ![P.port i 0,P.port i 1,P.port j 0,P.port j 1]

theorem pairing_classify {i j : P.Interior} (hij : i ≠ j) (hc : P.cell i = P.cell j) :
    P.pairing i j = qmaCrossPortPairing ∨ P.pairing i j = qmaCornerPortPairing false ∨
      P.pairing i j = qmaCornerPortPairing true :=
  qmaPortPairing_classify _ (P.two_visits_port_injective hij hc)

def IsCrossing (p : ℕ × ℕ) : Prop :=
  ∃ i j : P.Interior, i ≠ j ∧ P.cell i = p ∧ P.cell j = p ∧ P.pairing i j = qmaCrossPortPairing

def crossingCells : Finset (ℕ × ℕ) := (Finset.univ.image P.cell).filter P.IsCrossing

@[simp] theorem mem_crossingCells {p : ℕ × ℕ} : p ∈ P.crossingCells ↔ P.IsCrossing p := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    obtain ⟨i,j,hij,hi,hj,hp⟩ := h
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩,i,j,hij,hi,hj,hp⟩

theorem crossingCells_card : P.crossingCells.card ≤ ∑ e, (P.length e-1) := by
  calc
    _ ≤ (Finset.univ.image P.cell).card := Finset.card_filter_le _ _
    _ ≤ Fintype.card P.Interior := (Finset.card_image_le).trans_eq (Finset.card_univ)
    _ = _ := by simp [Interior,Fintype.card_sigma]

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
