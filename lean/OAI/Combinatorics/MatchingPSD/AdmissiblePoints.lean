import OAI.Combinatorics.MatchingPSD.CrossSelection

namespace OAI

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma triple_pairing_five {s : ℕ} (hs : 1 ≤ s) (j : Fin 5) :
    ∃ M : Pairing (TripleVertices s), crossVector tripleColor M =
      (![![1,0,0], ![0,1,1], ![3,0,0], ![1,2,0], ![1,0,2]] j : Fin 3 → ℝ) := by
  have hex (E : Fin 6 → ℕ) (he : endpointSizes E = ![2*s+1,2*s+1,2*s]) :
      ∃ M : Pairing (TripleVertices s), crossVector tripleColor M =
        (fun i => (![E 1,E 2,E 4] i : ℝ)) := by
    obtain ⟨M,hM⟩ := exists_pairing_of_endpoints tripleColor E (by rw [tripleColor_histogram, he])
    exact ⟨M,funext hM⟩
  fin_cases j
  · obtain ⟨M,hM⟩ := hex ![s,1,0,s,0,s] (by ext i; fin_cases i <;> simp [endpointSizes]; omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩
  · obtain ⟨M,hM⟩ := hex ![s,0,1,s,1,s-1] (by ext i; fin_cases i <;> simp [endpointSizes]; omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩
  · obtain ⟨M,hM⟩ := hex ![s-1,3,0,s-1,0,s] (by ext i; fin_cases i <;> simp [endpointSizes] <;> omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩
  · obtain ⟨M,hM⟩ := hex ![s-1,1,2,s,0,s-1] (by ext i; fin_cases i <;> simp [endpointSizes] <;> omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩
  · obtain ⟨M,hM⟩ := hex ![s,1,0,s-1,2,s-1] (by ext i; fin_cases i <;> simp [endpointSizes] <;> omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩

lemma triple_pairing_grid {s l d : ℕ} (hs : 2*l*d ≤ s) (k : Fin 3 → Fin (d+1)) :
    ∃ M : Pairing (TripleVertices s), crossVector tripleColor M =
      (fun a => (![1,0,0] a : ℝ) + (2*l:ℝ)*(k a:ℝ)) := by
  let E : Fin 6 → ℕ := ![s-l*((k 0:ℕ)+k 1), 1+2*l*k 0, 2*l*k 1,
    s-l*((k 0:ℕ)+k 2), 2*l*k 2, s-l*((k 1:ℕ)+k 2)]
  have hk (a : Fin 3) : (k a : ℕ) ≤ d := Nat.le_of_lt_succ (k a).isLt
  have hle (a b : Fin 3) : l*((k a:ℕ)+k b) ≤ s := by
    calc
      _ ≤ l*(d+d) := Nat.mul_le_mul_left l (Nat.add_le_add (hk a) (hk b))
      _ = 2*l*d := by ring
      _ ≤ s := hs
  have he : endpointSizes E = ![2*s+1,2*s+1,2*s] := by
    ext i
    fin_cases i <;> simp [endpointSizes, E]
    · have h := Nat.sub_add_cancel (hle 0 1); nlinarith
    · have h := Nat.sub_add_cancel (hle 0 2); nlinarith
    · have h := Nat.sub_add_cancel (hle 1 2); nlinarith
  obtain ⟨M,hM⟩ := exists_pairing_of_endpoints tripleColor E (by rw [tripleColor_histogram, he])
  refine ⟨M,?_⟩
  funext i
  rw [crossVector, hM]
  fin_cases i <;> simp [E, Nat.cast_add, Nat.cast_mul]

end MatchingSmoothing

end OAI
