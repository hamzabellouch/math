import Mathlib

namespace OAI

noncomputable section

namespace Problem315

theorem simpleGraph_subtype_card_le (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    Nat.card {G : SimpleGraph (Fin n) // P G} ≤ 2 ^ (n * n) := by
  classical
  let encode : {G : SimpleGraph (Fin n) // P G} → Fin n → Fin n → Bool :=
    fun G u v => decide (G.val.Adj u v)
  have hinj : Function.Injective encode := by
    intro G H h
    apply Subtype.ext
    apply SimpleGraph.ext
    funext u v
    apply propext
    exact decide_eq_decide.mp (congr_fun (congr_fun h u) v)
  have hcard := Fintype.card_le_of_injective encode hinj
  rw [Nat.card_eq_fintype_card]
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul] using hcard

end Problem315

end

end OAI
