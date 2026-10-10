import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortRouteData

namespace OAI

/-! A visit to an internal coarse cell occupies two different directional ports. -/

noncomputable section
namespace ContinuumCoulomb
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

abbrev Interior := Σ e : G.Edge, Fin (P.length e-1)

def cell (i : P.Interior) : ℕ × ℕ := P.point i.1 (i.2.val+1)

def armIndex (i : P.Interior) (a : Fin 2) : ℕ := i.2.val+2*a.val

def arm (i : P.Interior) (a : Fin 2) : ℕ × ℕ := P.point i.1 (P.armIndex i a)

theorem cell_index_lt (i : P.Interior) : i.2.val+1 < P.length i.1 := by
  have hi := i.2.isLt
  omega

theorem armIndex_le (i : P.Interior) (a : Fin 2) : P.armIndex i a ≤ P.length i.1 := by
  have hi := i.2.isLt
  have ha := a.isLt
  dsimp [armIndex]
  omega

theorem arm_adjacent (i : P.Interior) (a : Fin 2) : qmaSquareGrid.Adj (P.cell i) (P.arm i a) := by
  have hi := P.cell_index_lt i
  fin_cases a
  · exact (P.step i.1 i.2.val (by omega)).symm
  · exact P.step i.1 (i.2.val+1) hi

def port (i : P.Interior) (a : Fin 2) : Fin 4 := qmaGridNeighborIndex (P.cell i) (P.arm i a)

theorem port_spec (i : P.Interior) (a : Fin 2) :
    qmaGridNeighbor (P.cell i) (P.port i a) = P.arm i a :=
  qmaGridNeighborIndex_spec (P.positive i.1 _ (P.cell_index_lt i).le).1
    (P.positive i.1 _ (P.cell_index_lt i).le).2 (P.arm_adjacent i a)

theorem port_injective (i : P.Interior) : Function.Injective (P.port i) := by
  intro a b h
  have he := congrArg (qmaGridNeighbor (P.cell i)) h
  rw [P.port_spec,P.port_spec] at he
  have hi := P.simple i.1 (P.armIndex i a) (P.armIndex i b)
    (P.armIndex_le i a) (P.armIndex_le i b) he
  apply Fin.ext
  dsimp [armIndex] at hi
  omega

theorem cell_eq_same_edge {i j : P.Interior} (he : i.1 = j.1) (hc : P.cell i = P.cell j) : i = j := by
  rcases i with ⟨e,i⟩
  rcases j with ⟨f,j⟩
  dsimp only at he
  subst f
  have hi := P.simple e (i.val+1) (j.val+1) (P.cell_index_lt ⟨e,i⟩).le
    (P.cell_index_lt ⟨e,j⟩).le hc
  have hij : i = j := Fin.ext (by omega)
  subst j
  rfl

theorem incidence_injective : Function.Injective
    (fun x : P.Interior × Fin 2 => (P.cell x.1,P.port x.1 x.2)) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hc : P.cell i = P.cell j := congrArg Prod.fst h
  have hp : P.port i a = P.port j b := congrArg Prod.snd h
  have ha : P.arm i a = P.arm j b := by
    rw [← P.port_spec i a,← P.port_spec j b,hc,hp]
  have hij : i.1 = j.1 := by
    by_contra hef
    have hdis := P.edges_disjoint i.1 j.1 hef
    have hi := P.cell_index_lt i
    have hj := P.cell_index_lt j
    have hib := i.2.isLt
    have hjb := j.2.isLt
    fin_cases a <;> fin_cases b
    · exact (hdis i.2.val j.2.val (by omega) (by omega)).1 ⟨ha,hc⟩
    · exact (hdis i.2.val (j.2.val+1) (by omega) hj).2 ⟨ha,hc⟩
    · exact (hdis (i.2.val+1) j.2.val hi (by omega)).2 ⟨hc,ha⟩
    · exact (hdis (i.2.val+1) (j.2.val+1) hi hj).1 ⟨hc,ha⟩
  have he : i = j := P.cell_eq_same_edge hij hc
  subst j
  have hab : a = b := P.port_injective i hp
  subst b
  rfl

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
