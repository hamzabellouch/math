import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactSourceGrid

namespace OAI

/-! The canonical strip record has an explicit finite computation from its
two lattice endpoints. This identifies the selected record with the record used by rational
coordinate programs. -/

namespace ContinuumCoulomb

def canonicalContactEdge (p q : ℤ × ℤ) : ContactGridEdge :=
  let vertical := decide (p.1 = q.1)
  let forward := if vertical then decide (p.2 < q.2) else decide (p.1 < q.1)
  { vertical := vertical, anchor := if forward then p else q, reversed := !forward }

theorem canonicalContactEdge_endpoints (e : ContactGridEdge) :
    canonicalContactEdge e.left e.right = e := by
  rcases e with ⟨v, ⟨a, b⟩, r⟩
  cases v <;> cases r <;>
    simp [canonicalContactEdge, ContactGridEdge.left, ContactGridEdge.right,
      ContactGridEdge.upper]

theorem SquareLatticeHeisenberg.contactEdge_computation (d : SquareLatticeHeisenberg)
    (e : Fin d.edges) :
    d.contactEdge e = canonicalContactEdge (d.coordinate (d.left e)) (d.coordinate (d.right e)) := by
  rw [← d.contactEdge_left e, ← d.contactEdge_right e, canonicalContactEdge_endpoints]

end ContinuumCoulomb

end OAI
