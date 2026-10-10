import Mathlib
import OAI.Computability.SolenoidalRecorder.Rules

namespace OAI

/-! Finite recorder scans and the history frontier invariant. -/

namespace Solenoidal
namespace Recorder
variable {M : Machine}
inductive Steps : ℕ → Config M → Config M → Prop
  | zero (c : Config M) : Steps 0 c c
  | tail {n : ℕ} {c d e : Config M} : Steps n c d → Step d e → Steps (n + 1) c e

theorem Steps.one {c d : Config M} (h : Step c d) : Steps 1 c d :=
  .tail (.zero c) h

theorem Steps.trans {n m : ℕ} {c d e : Config M} (h₁ : Steps n c d) (h₂ : Steps m d e) :
    Steps (n + m) c e := by
  induction h₂ with
  | zero => simpa using h₁
  | tail h₂ hs ih => simpa only [Nat.add_assoc] using Steps.tail (ih h₁) hs

theorem scanRight_step (r : M.Instruction) (t : ℤ → Letter M) (k : ℤ)
    (hF : (t k).history ≠ .frontier) (hmark : (t k).mark = false) :
    Step ⟨.R r, k, t⟩ ⟨.R r, k + 1, t⟩ := by
  have hs : ⟨(t k).work, (t k).history, false⟩ = t k := by
    ext <;> simp [hmark]
  refine ⟨.R r, t k, .right, ?_, ?_⟩
  · change Rule M (.R r) (t k) (.R r) (t k) .right
    simpa only [hs] using Rule.scanRight r (t k).work (t k).history hF
  · simp [successor]

theorem scanLeft_step (q : M.State) (t : ℤ → Letter M) (k : ℤ)
    (hF : (t k).history ≠ .frontier) (hmark : (t k).mark = false) :
    Step ⟨.L q, k, t⟩ ⟨.L q, k - 1, t⟩ := by
  have hs : ⟨(t k).work, (t k).history, false⟩ = t k := by
    ext <;> simp [hmark]
  refine ⟨.L q, t k, .left, ?_, ?_⟩
  · change Rule M (.L q) (t k) (.L q) (t k) .left
    simpa only [hs] using Rule.scanLeft q (t k).work (t k).history hF
  · simp [successor, sub_eq_add_neg]

 
theorem scanRight_steps (r : M.Instruction) (t : ℤ → Letter M) (k : ℤ) (n : ℕ) :
    (∀ j : ℕ, j < n → (t (k + j)).history ≠ .frontier ∧ (t (k + j)).mark = false) →
    Steps n ⟨.R r, k, t⟩ ⟨.R r, k + n, t⟩ := by
  induction n with
  | zero => intro _; simpa using Steps.zero (⟨.R r, k, t⟩ : Config M)
  | succ n ih =>
    intro hg
    have hf := ih (fun j hj => hg j (by omega))
    have hl := scanRight_step r t (k + n) (hg n (by omega)).1 (hg n (by omega)).2
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hf.tail hl

theorem scanLeft_steps (q : M.State) (t : ℤ → Letter M) (k : ℤ) (n : ℕ) :
    (∀ j : ℕ, j < n → (t (k - j)).history ≠ .frontier ∧ (t (k - j)).mark = false) →
    Steps n ⟨.L q, k, t⟩ ⟨.L q, k - n, t⟩ := by
  induction n with
  | zero => intro _; simpa using Steps.zero (⟨.L q, k, t⟩ : Config M)
  | succ n ih =>
    intro hg
    have hf := ih (fun j hj => hg j (by omega))
    have hl := scanLeft_step q t (k - n) (hg n (by omega)).1 (hg n (by omega)).2
    simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using hf.tail hl

 
def tracks (W : ℤ → M.Symbol) (H : ℤ → History M) (b : ℤ → Bool) : ℤ → Letter M :=
  fun k => ⟨W k, H k, b k⟩

 
theorem tracks_step (W : ℤ → M.Symbol) (H : ℤ → History M) (b : ℤ → Bool) (k : ℤ)
    (s s' : Control M) (c : M.Symbol) (ℓ : History M) (v : Bool) (d : Move)
    (hr : Rule M s ⟨W k, H k, b k⟩ s' ⟨c, ℓ, v⟩ d) :
    Step ⟨s, k, tracks W H b⟩
      ⟨s', k + d.displacement,
        tracks (Function.update W k c) (Function.update H k ℓ) (Function.update b k v)⟩ := by
  refine ⟨s', ⟨c, ℓ, v⟩, d, hr, ?_⟩
  dsimp only [successor]
  apply Config.ext
  · rfl
  · rfl
  funext j
  by_cases hj : j = k
  · subst j; simp [tracks]
  · simp [tracks, hj]

 
def Frontier (H : ℤ → History M) (g : ℤ) : Prop :=
  (∀ k : ℤ, H k = .frontier ↔ k = g) ∧ (∀ k : ℤ, g < k → H k = .empty)

def appendHistory (H : ℤ → History M) (g : ℤ) (r : M.Instruction) : ℤ → History M :=
  Function.update (Function.update H g (.record r)) (g + 1) .frontier

theorem frontier_append {H : ℤ → History M} {g : ℤ} (h : Frontier H g) (r : M.Instruction) :
    Frontier (appendHistory H g r) (g + 1) := by
  constructor
  · intro k
    by_cases hk₁ : k = g + 1
    · subst k; simp [appendHistory]
    · by_cases hk₀ : k = g
      · subst k; simp [appendHistory, hk₁]
      · simp only [appendHistory, Function.update_of_ne hk₁, Function.update_of_ne hk₀]
        simp [h.1 k, hk₀, hk₁]
  · intro k hk
    have hk₁ : k ≠ g + 1 := by omega
    have hk₀ : k ≠ g := by omega
    simp [appendHistory, hk₁, hk₀, h.2 k (by omega)]

 
def initialHistory (g : ℤ) : ℤ → History M :=
  Function.update (fun _ => .empty) g .frontier

theorem frontier_initial (g : ℤ) : Frontier (initialHistory (M := M) g) g := by
  constructor
  · intro k
    by_cases hk : k = g
    · subst k; simp [initialHistory]
    · simp [initialHistory, hk]
  · intro k hk
    simp [initialHistory, ne_of_gt hk]
end Recorder
end Solenoidal

end OAI
