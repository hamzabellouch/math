import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialExecution

namespace OAI

namespace EditApproximation

 theorem arithmeticMapWithWork_total {α β : Type*} (f : α → β × ℕ) (values : List α) :
    (arithmeticMapWithWork f values).2 = (values.map (fun a => (f a).2)).sum + 3 * values.length := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [arithmeticMapWithWork, List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

namespace BinaryFraction

 theorem coarseMinimumWithWork_bounds (values : List BinaryFraction) (A : ℕ)
    (hA : 2 ≤ A) (hv : ∀ a ∈ values, a.width ≤ A) :
    (coarseMinimumWithWork values).1.width ≤ A ∧
      (coarseMinimumWithWork values).2 ≤ 1 + values.length * (1000 * (A + 1) ^ 2 + 2) := by
  cases values with
  | nil =>
    constructor
    · exact (nat_width_le 0).trans (by simpa using hA)
    · simp only [coarseMinimumWithWork, List.length_nil, zero_mul, add_zero, le_refl]
  | cons a rest =>
    have ha := hv a List.mem_cons_self
    have hr := fun b hb => hv b (List.mem_cons_of_mem _ hb)
    exact ⟨minimumWithWork_width a rest A ha hr,
      (minimumWithWork_cost a rest A ha hr).trans (by simp only [List.length_cons]; nlinarith)⟩

 theorem naturalListEqualWithWork_cost (x y : List ℕ) (S : ℕ)
    (hs : ∀ a ∈ x ++ y, Nat.size a ≤ S) :
    (naturalListEqualWithWork x y).2 ≤ (x.length + y.length + 1) * (8 * S + 4) := by
  induction x generalizing y with
  | nil => cases y <;> simp only [naturalListEqualWithWork] <;> nlinarith [Nat.zero_le S]
  | cons a left ih =>
    cases y with
    | nil => simp only [naturalListEqualWithWork]; nlinarith [Nat.zero_le S]
    | cons b right =>
      have ha : Nat.size a ≤ S := hs a (by simp)
      have hb : Nat.size b ≤ S := hs b (by simp)
      have ht := naturalEqualWithWork_cost a b S ha hb
      have hr := ih right (by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hs z (List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ hz)))
        · exact hs z (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hz))))
      simp only [naturalListEqualWithWork]
      split_ifs <;> dsimp only
      · simp only [List.length_cons] at *
        nlinarith only [ht, hr, Nat.zero_le S]
      · simp only [List.length_cons]
        nlinarith only [ht, Nat.zero_le S, Nat.zero_le left.length, Nat.zero_le right.length]

end BinaryFraction
end EditApproximation

end OAI
