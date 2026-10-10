import OAI.NumberTheory.TwoPoint.Bounds.ProgressionEdgeGate

namespace OAI

/-! On a genuine increasing edge, the symmetric gate is precisely the
original progression restriction for that edge's padding divisor. -/

namespace TwoPointCorrelations

lemma progressionEdgeGate_on_edge (h l b d q : ℕ) (hh : 0 < h) (hd : 0 < d)
    (hq : 0 < q) (n : ℤ) :
    progressionEdgeGate h l b d n (n + (h * q * d : ℕ)) ↔
      Int.ModEq (l : ℤ) n (b * q * d : ℕ) := by
  constructor
  · rintro ⟨q', hf | hr⟩
    · have he : h * q * d = h * q' * d := by
        exact_mod_cast add_left_cancel hf.1
      have hq' : q = q' := Nat.eq_of_mul_eq_mul_left hh
        (Nat.eq_of_mul_eq_mul_right hd he)
      simpa only [← hq'] using hf.2
    · have hpos : (0 : ℤ) < (h * q * d : ℕ) := by positivity
      have hnneg : (0 : ℤ) ≤ (h * q' * d : ℕ) := by positivity
      omega
  · intro he
    exact ⟨q, Or.inl ⟨rfl, he⟩⟩

end TwoPointCorrelations

end OAI
