import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPermittedRouteSeparation

namespace OAI

/-! A catalog path stays in the cells of its two endpoints. This transfers
positivity and box bounds from physical spins to all subdivision sites. -/

namespace ContinuumCoulomb

theorem qmaLocalPort_bounded (b : Bool) (a : Fin 4) :
    (qmaLocalPort b a).1 < 32 ∧ (qmaLocalPort b a).2 < 32 := by
  cases b <;> fin_cases a <;> decide

theorem qmaPointCell_localPort (p : ℕ × ℕ) (b : Bool) (a : Fin 4) :
    qmaPointCell (qmaCellTranslate p (qmaLocalPort b a)) = p :=
  qmaCellTranslate_cell p _ (qmaLocalPort_bounded b a)

theorem qmaPointCell_halfPath {p z : ℕ × ℕ} {b : Bool} {a : Fin 4}
    (hz : z ∈ qmaHalfPathAt p b a) : qmaPointCell z = p := by
  obtain ⟨u,hu,hv,rfl⟩ := qmaHalfPathAt_mem hz
  exact qmaCellTranslate_cell p u ⟨hu,hv⟩

theorem qmaPointCell_internalPath {p z : ℕ × ℕ} {e : QMAInternalEdge}
    (hz : z ∈ (qmaInternalBody p e).path) : qmaPointCell z = p := by
  rw [qmaInternalBody_path] at hz
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hz
  exact qmaCellTranslate_cell p u (qmaInternalPath_bounded e u hu)

namespace QMACellRouteBody

theorem path_cells (R : QMACellRouteBody) {z : ℕ × ℕ} (hz : z ∈ R.path) :
    qmaPointCell z = qmaPointCell R.source ∨ qmaPointCell z = qmaPointCell R.target := by
  rcases qmaCellBody_cases R with ⟨p,e,rfl⟩ | ⟨p,a,b,c,rfl⟩
  · have hp := qmaPointCell_internalPath hz
    have hs := qmaPointCell_internalPath (List.mem_of_head? (qmaInternalBody p e).endpoints.1)
    exact Or.inl (hp.trans hs.symm)
  · rcases List.mem_append.mp hz with h | h
    · have hp := qmaPointCell_halfPath h
      exact Or.inl (hp.trans (qmaPointCell_localPort p b a).symm)
    · have hp := qmaPointCell_halfPath (List.mem_reverse.mp h)
      exact Or.inr (hp.trans (qmaPointCell_localPort (qmaGridNeighbor p a) c (qmaPortOpposite a)).symm)

end QMACellRouteBody
namespace QMACellRoute

theorem path_cells (R : QMACellRoute) {z : ℕ × ℕ} (hz : z ∈ R.path) :
    qmaPointCell z = qmaPointCell R.source ∨ qmaPointCell z = qmaPointCell R.target := by
  rcases R with ⟨R,b⟩
  cases b
  · exact R.path_cells hz
  · have h := R.path_cells (List.mem_reverse.mp hz)
    exact h.elim Or.inr Or.inl

theorem path_positive (R : QMACellRoute)
    (hs : 0 < (qmaPointCell R.source).1 ∧ 0 < (qmaPointCell R.source).2)
    (ht : 0 < (qmaPointCell R.target).1 ∧ 0 < (qmaPointCell R.target).2)
    {z : ℕ × ℕ} (hz : z ∈ R.path) : 0 < z.1 ∧ 0 < z.2 := by
  have hp : 0 < (qmaPointCell z).1 ∧ 0 < (qmaPointCell z).2 := by
    rcases R.path_cells hz with h | h
    · simpa only [h] using hs
    · simpa only [h] using ht
  change 0 < z.1/32 ∧ 0 < z.2/32 at hp
  omega

theorem path_bounded (R : QMACellRoute) {X Y : ℕ}
    (hs : R.source.1 < 32*X ∧ R.source.2 < 32*Y)
    (ht : R.target.1 < 32*X ∧ R.target.2 < 32*Y)
    {z : ℕ × ℕ} (hz : z ∈ R.path) : z.1 < 32*X ∧ z.2 < 32*Y := by
  have hp : (qmaPointCell z).1 < X ∧ (qmaPointCell z).2 < Y := by
    rcases R.path_cells hz with h | h
    · rw [h]
      change R.source.1/32 < X ∧ R.source.2/32 < Y
      omega
    · rw [h]
      change R.target.1/32 < X ∧ R.target.2/32 < Y
      omega
  change z.1/32 < X ∧ z.2/32 < Y at hp
  omega

end QMACellRoute
end ContinuumCoulomb

end OAI
