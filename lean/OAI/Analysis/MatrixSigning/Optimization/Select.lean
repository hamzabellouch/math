import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.Descent
variable {α : Type*}

def select (score : α → ℚ) (a : α) : List α → α
  | [] => a
  | b :: bs => select score (if score b < score a then b else a) bs

lemma select_mem (score : α → ℚ) (a : α) (l : List α) : select score a l ∈ a :: l := by
  induction l generalizing a with
  | nil => simp [select]
  | cons b bs ih =>
    rw [select]
    split
    · have hh := ih b
      simp only [List.mem_cons] at hh ⊢
      tauto
    · have hh := ih a
      simp only [List.mem_cons] at hh ⊢
      tauto

lemma select_le (score : α → ℚ) (a : α) (l : List α) :
    ∀ b ∈ a :: l, score (select score a l) ≤ score b := by
  induction l generalizing a with
  | nil => simp [select]
  | cons b bs ih =>
    rw [select]
    split
    · rename_i h
      intro c hc
      have hb := ih b b (by simp)
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · exact hb.trans h.le
      · exact hb
      · exact ih b c (by simp [hc])
    · rename_i h
      intro c hc
      have ha := ih a a (by simp)
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · exact ha
      · exact ha.trans (le_of_not_gt h)
      · exact ih a c (by simp [hc])

theorem select_value_bound (f : α → ℝ) (score : α → ℚ) (a : α) (l : List α)
    {e : ℝ} (herr : ∀ b ∈ a :: l, |(score b:ℝ)-f b| ≤ e) :
    ∀ b ∈ a :: l, f (select score a l) ≤ f b+2*e := by
  intro b hb
  have hs := abs_le.mp (herr (select score a l) (select_mem score a l))
  have ht := abs_le.mp (herr b hb)
  have hm : (score (select score a l):ℝ) ≤ (score b:ℝ) := by exact_mod_cast select_le score a l b hb
  linarith

theorem select_decrease (f : α → ℝ) (score : α → ℚ) (x a : α) (l : List α)
    {Δ : ℝ} (herr : ∀ b ∈ a :: l, |(score b:ℝ)-f b| ≤ Δ/4)
    (hgood : ∃ b ∈ a :: l, f b ≤ f x-2*Δ) :
    f (select score a l) ≤ f x-3*Δ/2 := by
  obtain ⟨b,hb,hf⟩ := hgood
  have hs := select_value_bound f score a l herr b hb
  linarith

def run (step : α → Option α) : ℕ → α → α
  | 0,x => x
  | k+1,x => match step x with
    | none => x
    | some y => run step k y

lemma run_invariant (step : α → Option α) (P : α → Prop)
    (hp : ∀ x y,P x → step x=some y → P y) (k : ℕ) (x : α) (hx : P x) :
    P (run step k x) := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih =>
    simp only [run]
    split
    · exact hx
    · rename_i y hy
      exact ih y (hp x y hx hy)

theorem run_terminates (step : α → Option α) (P : α → Prop) (f : α → ℝ) {r : ℝ}
    (hr : 0 < r) (hf : ∀ x,P x → 0 ≤ f x)
    (hp : ∀ x y,P x → step x=some y → P y)
    (hd : ∀ x y,P x → step x=some y → f y ≤ f x-r)
    (k : ℕ) (x : α) (hx : P x) (hk : f x < k*r) : step (run step k x)=none := by
  induction k generalizing x with
  | zero => simp only [Nat.cast_zero,zero_mul] at hk; exact (not_lt_of_ge (hf x hx) hk).elim
  | succ k ih =>
    rw [run]
    cases he : step x with
    | none => exact he
    | some y =>
      apply ih y (hp x y hx he)
      have hdecrease := (div_le_div_iff_of_pos_right hr).2 (hd x y hx he)
      have hbound := (div_lt_iff₀ hr).2 hk
      apply (div_lt_iff₀ hr).1
      rw [sub_div, div_self (ne_of_gt hr)] at hdecrease
      push_cast at hbound
      linarith

end CurrentKS.Descent

end OAI
