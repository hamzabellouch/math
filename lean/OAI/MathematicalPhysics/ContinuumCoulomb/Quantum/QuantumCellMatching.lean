import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellPassages
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortPairing

namespace OAI

/-! Internal visits form a matching on the four ports of each cell. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

abbrev CellVisits (p : ℕ × ℕ) := {i : P.Interior // P.cell i = p}

def cellPort (p : ℕ × ℕ) (x : P.CellVisits p × Fin 2) : Fin 4 := P.port x.1.val x.2

theorem cellPort_injective (p : ℕ × ℕ) : Function.Injective (P.cellPort p) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have he : (i.val,a) = (j.val,b) := P.incidence_injective (Prod.ext (i.property.trans j.property.symm) h)
  have hi : i = j := Subtype.ext (congrArg Prod.fst he)
  have hab : a = b := congrArg Prod.snd he
  exact Prod.ext hi hab

theorem cellVisits_card (p : ℕ × ℕ) : Fintype.card (P.CellVisits p) ≤ 2 := by
  have h := Fintype.card_le_of_injective (P.cellPort p) (P.cellPort_injective p)
  simp only [Fintype.card_prod,Fintype.card_fin] at h
  omega

theorem different_visits_ports {i j : P.Interior} (hij : i ≠ j) (hc : P.cell i = P.cell j)
    (a b : Fin 2) : P.port i a ≠ P.port j b := by
  intro h
  have he : (i,a) = (j,b) := P.incidence_injective (Prod.ext hc h)
  exact hij (congrArg Prod.fst he)

theorem two_visits_port_injective {i j : P.Interior} (hij : i ≠ j) (hc : P.cell i = P.cell j) :
    Function.Injective (![P.port i 0,P.port i 1,P.port j 0,P.port j 1] : Fin 4 → Fin 4) := by
  have hi : P.port i 0 ≠ P.port i 1 := (P.port_injective i).ne (by decide)
  have hj : P.port j 0 ≠ P.port j 1 := (P.port_injective j).ne (by decide)
  have h00 := P.different_visits_ports hij hc 0 0
  have h01 := P.different_visits_ports hij hc 0 1
  have h10 := P.different_visits_ports hij hc 1 0
  have h11 := P.different_visits_ports hij hc 1 1
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all

def twoVisitsEquiv {i j : P.Interior} (hij : i ≠ j) (hc : P.cell i = P.cell j) : Fin 4 ≃ Fin 4 :=
  Equiv.ofBijective ![P.port i 0,P.port i 1,P.port j 0,P.port j 1]
    ⟨P.two_visits_port_injective hij hc,Finite.surjective_of_injective (P.two_visits_port_injective hij hc)⟩

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
