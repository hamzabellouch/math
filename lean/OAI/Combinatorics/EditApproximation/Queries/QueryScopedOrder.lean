import OAI.Combinatorics.EditApproximation.Queries.QueryOrderBounds

namespace OAI

/-! Sorting costs only require bounded comparisons between keys actually
present in the input.  This is needed for the natural-valued history time. -/

namespace EditApproximation

theorem memberByWithWork_cost_on {α : Type*} (P : α → Prop)
    (equal : α → α → Bool × ℕ) (C : ℕ)
    (hC : ∀ a, P a → ∀ b, P b → (equal a b).2 ≤ C)
    (a : α) (ha : P a) (xs : List α) (hx : ∀ b ∈ xs, P b) :
    (memberByWithWork equal a xs).2 ≤ 1 + xs.length * (C + 1) := by
  induction xs with
  | nil => simp only [memberByWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_refl]
  | cons b xs ih =>
    have h := hC a ha b (hx b (by simp))
    have ht := ih (fun c hc => hx c (List.mem_cons_of_mem b hc))
    change _ + _ + 1 ≤ _
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem queryEraseLoopWithWork_cost_on {α : Type*} (P : α → Prop)
    (equal : α → α → Bool × ℕ) (C : ℕ)
    (hC : ∀ a, P a → ∀ b, P b → (equal a b).2 ≤ C)
    (xs seen : List α) (hx : ∀ a ∈ xs, P a) (hs : ∀ a ∈ seen, P a) :
    (queryEraseLoopWithWork equal xs seen).2 ≤
      (xs.length + 1) * (xs.length + seen.length + 1) * (C + 4) := by
  induction xs generalizing seen with
  | nil =>
    simp only [queryEraseLoopWithWork, List.length_nil, zero_add, one_mul]
    nlinarith
  | cons a xs ih =>
    have ha := hx a (by simp)
    have hm := memberByWithWork_cost_on P equal C hC a ha seen hs
    let next := if (memberByWithWork equal a seen).1 then seen else a :: seen
    have hn : ∀ b ∈ next, P b := by
      intro b hb
      dsimp only [next] at hb
      split_ifs at hb
      · exact hs b hb
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hs b hb
    have hl : next.length ≤ seen.length + 1 := by
      dsimp only [next]
      split <;> (try simp only [List.length_cons]) <;> omega
    have hi := ih next (fun b hb => hx b (List.mem_cons_of_mem a hb)) hn
    have hh : (queryEraseLoopWithWork equal xs next).2 ≤
        (xs.length + 1) * (xs.length + (seen.length + 1) + 1) * (C + 4) :=
      hi.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
    change (memberByWithWork equal a seen).2 + (queryEraseLoopWithWork equal xs next).2 + 2 ≤ _
    simp only [List.length_cons]
    nlinarith only [hm, hh, Nat.zero_le xs.length, Nat.zero_le seen.length, Nat.zero_le C]

theorem queryEraseWithWork_cost_on {α : Type*} (P : α → Prop)
    (equal : α → α → Bool × ℕ) (C : ℕ)
    (hC : ∀ a, P a → ∀ b, P b → (equal a b).2 ≤ C)
    (xs : List α) (hx : ∀ a ∈ xs, P a) :
    (queryEraseWithWork equal xs).2 ≤ (xs.length + 1) ^ 2 * (C + 4) := by
  simpa only [queryEraseWithWork, List.length_nil, Nat.add_zero, pow_two] using
    queryEraseLoopWithWork_cost_on P equal C hC xs [] hx (by simp)

theorem queryInsertWithWork_cost_on {α : Type*} (P : α → Prop)
    (le : α → α → Bool × ℕ) (C : ℕ)
    (hC : ∀ a, P a → ∀ b, P b → (le a b).2 ≤ C)
    (a : α) (ha : P a) (xs : List α) (hx : ∀ b ∈ xs, P b) :
    (queryInsertWithWork le a xs).2 ≤ (xs.length + 1) * (C + 2) := by
  induction xs with
  | nil => simp only [queryInsertWithWork, List.length_nil]; omega
  | cons b xs ih =>
    have h := hC a ha b (hx b (by simp))
    have ht := ih (fun c hc => hx c (List.mem_cons_of_mem b hc))
    simp only [queryInsertWithWork, List.length_cons]
    split <;> dsimp only
    · nlinarith only [h, Nat.zero_le xs.length, Nat.zero_le C]
    · nlinarith only [h, ht]

theorem querySortWithWork_cost_on {α : Type*} (P : α → Prop)
    (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b))
    (C : ℕ) (hC : ∀ a, P a → ∀ b, P b → (le a b).2 ≤ C)
    (xs : List α) (hx : ∀ a ∈ xs, P a) :
    (querySortWithWork le xs).2 ≤ (xs.length + 1) ^ 2 * (C + 3) := by
  induction xs with
  | nil => simp only [querySortWithWork, List.length_nil]; omega
  | cons a xs ih =>
    have ht := ih (fun b hb => hx b (List.mem_cons_of_mem a hb))
    have hs : ∀ b ∈ (querySortWithWork le xs).1, P b := by
      intro b hb
      rw [querySortWithWork_value r le hle, List.mem_insertionSort] at hb
      exact hx b (List.mem_cons_of_mem a hb)
    have hi := queryInsertWithWork_cost_on P le C hC a (hx a (by simp))
      (querySortWithWork le xs).1 hs
    have hl : (querySortWithWork le xs).1.length = xs.length := by
      rw [querySortWithWork_value r le hle, List.length_insertionSort]
    rw [hl] at hi
    change (querySortWithWork le xs).2 + _ + 1 ≤ _
    simp only [List.length_cons]
    nlinarith only [ht, hi, Nat.zero_le xs.length, Nat.zero_le C]

theorem queryOrderedInputsWithWork_cost_on {α : Type*} [DecidableEq α]
    (P : α → Prop) (encode : α → ℕ) (equal le : α → α → Bool × ℕ)
    (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (hle : ∀ a b, (le a b).1 = decide (encode a ≤ encode b))
    (C D : ℕ) (hequal : ∀ a, P a → ∀ b, P b → (equal a b).2 ≤ C)
    (horder : ∀ a, P a → ∀ b, P b → (le a b).2 ≤ D)
    (xs : List α) (hx : ∀ a ∈ xs, P a) :
    (queryOrderedInputsWithWork equal le xs).2 ≤ (xs.length + 1) ^ 2 * (C + D + 8) := by
  have he := queryEraseWithWork_cost_on P equal C hequal xs hx
  have hu : ∀ a ∈ (queryEraseWithWork equal xs).1, P a := by
    intro a ha
    rw [queryEraseWithWork_value equal heq, List.mem_eraseDups] at ha
    exact hx a ha
  have hs := querySortWithWork_cost_on P (fun a b => encode a ≤ encode b)
    le hle D horder (queryEraseWithWork equal xs).1 hu
  have hl := queryEraseWithWork_length equal xs
  have hp : ((queryEraseWithWork equal xs).1.length + 1) ^ 2 ≤ (xs.length + 1) ^ 2 := by
    gcongr
  have hb := hs.trans (Nat.mul_le_mul_right (D + 3) hp)
  change (queryEraseWithWork equal xs).2 + _ + 1 ≤ _
  nlinarith only [he, hb, Nat.zero_le C, Nat.zero_le D, Nat.zero_le xs.length]

end EditApproximation

end OAI
