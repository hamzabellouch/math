import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellCrossings
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortSpinCoverage

namespace OAI

/-! Every terminal of every selected crossing is an actual spin in the completed
rational port graph. Distinct crossing cells have disjoint terminal sets. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

abbrev Crossing := {p : ℕ × ℕ // p ∈ P.crossingCells}

abbrev finishedGraph (N : ℚ) (D : ℕ) : QMARationalExchangeGraph := (P.schedule.iterate N D).graph

def finishedPosition (N : ℚ) (D : ℕ) : Fin (P.finishedGraph N D).n → ℕ × ℕ :=
  (P.toEmbedding.iterate N D).position

theorem crossing_terminal_exists (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (c : P.Crossing) (a : Fin 4) :
    ∃ v, P.finishedPosition N D v = qmaGridPort c.val a := by
  obtain ⟨i,j,hij,hi,hj,_⟩ := P.mem_crossingCells.mp c.property
  have hc : P.cell i = P.cell j := hi.trans hj.symm
  obtain ⟨b,hb⟩ := (P.twoVisitsEquiv hij hc).surjective a
  fin_cases b
  · change P.port i 0 = a at hb
    simpa only [finishedPosition,hi,hb] using P.iterate_covers_port N hD i 0
  · change P.port i 1 = a at hb
    simpa only [finishedPosition,hi,hb] using P.iterate_covers_port N hD i 1
  · change P.port j 0 = a at hb
    simpa only [finishedPosition,hj,hb] using P.iterate_covers_port N hD j 0
  · change P.port j 1 = a at hb
    simpa only [finishedPosition,hj,hb] using P.iterate_covers_port N hD j 1

def crossingSite (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (c : P.Crossing) (a : Fin 4) :
    Fin (P.finishedGraph N D).n := Classical.choose (P.crossing_terminal_exists N hD c a)

theorem crossingSite_spec (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (c : P.Crossing) (a : Fin 4) :
    P.finishedPosition N D (P.crossingSite N hD c a) = qmaGridPort c.val a :=
  Classical.choose_spec (P.crossing_terminal_exists N hD c a)

theorem crossingSite_injective (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) :
    Function.Injective (fun x : P.Crossing × Fin 4 => P.crossingSite N hD x.1 x.2) := by
  rintro ⟨c,a⟩ ⟨d,b⟩ h
  have hp := congrArg (P.finishedPosition N D) h
  rw [P.crossingSite_spec,P.crossingSite_spec] at hp
  have he : (c.val,a) = (d.val,b) := qmaGridPort_injective hp
  have hcd : c = d := Subtype.ext (congrArg (fun z : (ℕ × ℕ) × Fin 4 => z.1) he)
  have hab : a = b := congrArg (fun z : (ℕ × ℕ) × Fin 4 => z.2) he
  exact Prod.ext hcd hab

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
