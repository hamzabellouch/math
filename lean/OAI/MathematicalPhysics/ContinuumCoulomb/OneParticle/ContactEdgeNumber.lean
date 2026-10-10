import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactMediator

namespace OAI

/-! Natural-number formulas for the exact final-edge permutation. These
are the indices used to fetch calibrated lengths from the emitted list. -/

namespace ContinuumCoulomb.ContactMediator

def pathNumber (r e : ℕ) : LocalPath → ℕ
  | Sum.inl s => e * 2 + s.val
  | Sum.inr (s, t) => r * 2 + (e * 2 + s.val) * 2 + t.val

def edgeNumber (r e : ℕ) : LocalEdge → ℕ
  | Sum.inl _ => e
  | Sum.inr (Sum.inl p) => r + pathNumber r e p
  | Sum.inr (Sum.inr (p, t)) => r + (r * 2 + r * 2 * 2) + pathNumber r e p * 2 + t.val

theorem pathIndex_val (r : ℕ) (e : Fin r) (p : LocalPath) :
    (pathIndex r e p).val = pathNumber r e.val p := by
  rcases p with s | ⟨s, t⟩ <;>
    simp [pathIndex, pathNumber, spokeIndex, finProdFinEquiv] <;> ring

theorem encodeEdge_val (r : ℕ) (e : Fin r) (a : LocalEdge) :
    (encodeEdge r e a).val = edgeNumber r e.val a := by
  rcases a with u | (p | ⟨p, t⟩)
  · simp [encodeEdge, edgeNumber]
  · simp [encodeEdge, edgeNumber, pathIndex_val]
  · simp [encodeEdge, edgeNumber, spokeIndex, finProdFinEquiv, pathIndex_val, Nat.add_assoc]
    ring

end ContinuumCoulomb.ContactMediator

end OAI
