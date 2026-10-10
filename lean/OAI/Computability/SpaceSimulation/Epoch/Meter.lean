import OAI.Computability.SpaceSimulation.Epoch.Nodes

namespace OAI

namespace Fifths.Tour
variable (D : Tour)

attribute [local irreducible] Fifths.Circuit.price
theorem coins_array {e i} (l : e<D.E) (h : i < D.N) :
    D.coins (D.mkV e i) = e*D.per := by
  simp [coins, D.ae l h,D.ac l h,h]

theorem coins_history {e i} (l : e<D.E) (h : i ≤ D.k) :
    D.coins (D.hV e i) = e*D.per + D.coinsHard + (i+1)*D.coinsEasy := by
  simp [coins,D.he l h,D.hc l h,D.hr l h]

-- Both kinds at once. Charge a retained Y only on a call into an array
-- column of this epoch.
theorem supplied (v : D.Vertex) (p : D.baseOf v = false) :
    D.coins (D.header v) + D.coinsEasy ≤ D.coins v ∧
    (∀ i < D.N, D.coins (D.childrenOf v i) + D.circuit.price (D.guesses v) ≤ D.coins v) := by
  rcases D.either v with ⟨e,l,j,b,rfl⟩|⟨e,l,j,b,rfl⟩
  · cases e with
    | zero => simp [baseOf,D.ae l b,D.ac l b,b.le] at p
    | succ e =>
      have h : e<D.E := by omega
      simp only [coins_array D l b,guesses,header,childrenOf,D.ac l b,D.ae l b,b,b.le,
        ↓reduceIte,Nat.add_sub_cancel,coins_array D h b,coins_history D h le_rfl,show D.circuit.price 0 = D.coinsEasy from rfl]
      constructor
      · unfold per
        nlinarith
      · intro i _
        unfold per
        nlinarith
  · cases j with
    | zero =>
      cases e with
      | zero => simp [baseOf,D.he l b,D.hc l b] at p
      | succ e =>
        have f : D.col (D.hV (e+1) 0) = D.N := D.hc l b
        have h : e<D.E := by omega
        simp only [coins_history D l b,guesses,header,childrenOf,f,D.he l b,le_refl,
          lt_self_iff_false,↓reduceIte,Nat.add_sub_cancel,coins_history D h le_rfl,show D.circuit.price 0 = D.coinsEasy from rfl]
        constructor
        · unfold per; nlinarith
        · intro i _
          unfold per; nlinarith
    | succ j =>
      have f : D.col (D.hV e (j+1)) > D.N := by rw [D.hc l b]; omega
      have q : j ≤ D.k := by omega
      simp only [header,guesses,childrenOf,D.he l b,D.hr l b,not_le.mpr f,Nat.not_lt.mpr f.le,
        Ne.symm f.ne,↓reduceIte,Nat.add_sub_cancel,coins_history D l b,coins_history D l q,
        show D.circuit.price D.guessLength = D.coinsHard from rfl]
      constructor
      · nlinarith
      · intro i u; rw [D.coins_array l u]; omega

theorem covers : D.circuit.Meter D.coins where
  cheap := fun v h => (D.supplied v h).1
  expensive := fun v h => (D.supplied v h).2

theorem coins_total (v : D.Vertex) : D.coins v ≤ D.E * D.per := by
  obtain (⟨e,l,j,b,rfl⟩|⟨e,l,j,b,rfl⟩) := D.either v
  · rw [D.coins_array l b]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt l)
  · rw [D.coins_history l b]
    calc
      _ ≤ (e+1)*D.per := by unfold per; nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ l
end Fifths.Tour

end OAI
