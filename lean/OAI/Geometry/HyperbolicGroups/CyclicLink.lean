import Mathlib

namespace OAI

section
section


/-! Finite cyclic-link counting used at the literal fan apices.  No planarity,
normal-form, or diagram conclusions are postulated here. -/
noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FanLink

inductive State
  | absent | triangle | other | dominant
  deriving DecidableEq

namespace State

def active : State → Bool
  | absent => false
  | _ => true

def d : State → ℕ
  | dominant => 1
  | _ => 0

def n : State → ℕ
  | other => 1
  | _ => 0

def f : State → ℕ
  | triangle => 1
  | _ => 0

def turn : State → ℕ
  | other | dominant => 1
  | _ => 0

def bit (b : Bool) : ℕ := if b then 1 else 0

def boundary (a b : State) : ℕ := if a.active = b.active then 0 else 1

lemma endpoint_bound (a b : State) (L : Bool)
    (h : ¬ (a = dominant ∧ b = dominant)) :
    d a + d b ≤ n a + n b + f a * bit L + f b * bit L +
      turn a * bit (!L) + turn b * bit (!L) + boundary a b := by
  cases a <;> cases b <;> cases L <;>
    simp_all [d,n,f,turn,bit,boundary,active]

lemma fan_partition (s : State) (L R : Bool)
    (h : s = triangle → L ≠ R) :
    f s * bit L + f s * bit R = f s := by
  cases s <;> cases L <;> cases R <;> simp_all [f,bit]

end State
open State

variable {V : Type*} [Fintype V]

def D (s : V → State) : ℕ := ∑ i, (s i).d
def N (s : V → State) : ℕ := ∑ i, (s i).n
def Q (s : V → State) : ℕ := ∑ i, (s i).f
def P (next : Equiv.Perm V) (s : V → State) (line : V → Bool) : ℕ :=
  ∑ i, (s i).turn * (bit (!(line i)) + bit (!(line (next i))))
def B (next : Equiv.Perm V) (s : V → State) : ℕ :=
  ∑ i, State.boundary (s i) (s (next i))

/-- Direct endpoint charging proves the dominant-turn bound. A selected
triangle has one line endpoint. A nonline endpoint of a top turn incurs its
exceptional loose-side payment. No two dominant turns share a radial side.
This works even before the five-step bound and allows any selection of steps. -/
theorem dominant_endpoint_bound (next : Equiv.Perm V) (s : V → State) (line : V → Bool)
    (hcancel : ∀ i, ¬ (s i = dominant ∧ s (next i) = dominant))
    (hbip : ∀ i, s i = triangle → line i ≠ line (next i)) :
    2 * D s ≤ 2 * N s + Q s + P next s line + B next s := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => endpoint_bound (s i) (s (next i)) (line (next i)) (hcancel i))
  have hfan : (∑ i, (s i).f * bit (line i)) +
      (∑ i, (s i).f * bit (line (next i))) = Q s := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => fan_partition _ _ _ (hbip i))
  have hpay : (∑ i, (s i).turn * bit (!(line i))) +
      (∑ i, (s i).turn * bit (!(line (next i)))) = P next s line := by
    simp only [P,Nat.mul_add,Finset.sum_add_distrib]
  simp only [Finset.sum_add_distrib] at h
  rw [Equiv.sum_comp next (fun i => (s i).d),
    Equiv.sum_comp next (fun i => (s i).n),
    Equiv.sum_comp next (fun i => (s i).f * bit (line i)),
    Equiv.sum_comp next (fun i => (s i).turn * bit (!(line i)))] at h
  dsimp [D,N,B] at *
  omega

/-- One connected cyclic order, including the one-element cycle. -/
def IsCyclic (next : Equiv.Perm V) : Prop :=
  ∀ i j, ∃ k : ℕ, (next ^ k) i = j

def enter (a b : Bool) : ℕ := if a = false ∧ b = true then 1 else 0
def leave (a b : Bool) : ℕ := if a = true ∧ b = false then 1 else 0

lemma transition_balance (a b : Bool) : bit a + enter a b = bit b + leave a b := by
  cases a <;> cases b <;> decide

lemma transition_split (a b : State) :
    boundary a b = enter a.active b.active + leave a.active b.active := by
  cases a <;> cases b <;> decide

lemma total_balance (next : Equiv.Perm V) (sel : V → Bool) :
    (∑ i, enter (sel i) (sel (next i))) = ∑ i, leave (sel i) (sel (next i)) := by
  have h := congrArg (fun f : V → ℕ => ∑ i, f i)
    (funext (fun i => transition_balance (sel i) (sel (next i))))
  simp only [Finset.sum_add_distrib] at h
  rw [Equiv.sum_comp next (fun i => bit (sel i))] at h
  omega

lemma boundary_eq_twice (next : Equiv.Perm V) (s : V → State) :
    B next s = 2 * ∑ i, leave (s i).active (s (next i)).active := by
  simp only [B,transition_split,Finset.sum_add_distrib,total_balance,two_mul]

lemma boundary_le_four (next : Equiv.Perm V) (s : V → State)
    (hcard : Fintype.card V ≤ 5) : B next s ≤ 4 := by
  have ha : (∑ i, leave (s i).active (s (next i)).active) ≤ ∑ i, bit (s i).active := by
    apply Finset.sum_le_sum
    intro i _
    cases h : (s i).active <;> cases h' : (s (next i)).active <;> decide
  have hb : (∑ i, enter (s i).active (s (next i)).active) ≤ ∑ i, bit (!(s i).active) := by
    apply Finset.sum_le_sum
    intro i _
    cases h : (s i).active <;> cases h' : (s (next i)).active <;> decide
  have hab : (∑ i, bit (s i).active) + (∑ i, bit (!(s i).active)) = Fintype.card V := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : V, 1 := Finset.sum_congr rfl (fun i _ => by cases (s i).active <;> decide)
      _ = _ := by simp
  rw [total_balance] at hb
  rw [boundary_eq_twice]
  omega

lemma selected_of_no_leave (next : Equiv.Perm V) (sel : V → Bool)
    (hz : (∑ i, leave (sel i) (sel (next i))) = 0) {i : V} (hi : sel i = true) :
    sel (next i) = true := by
  have hz' : leave (sel i) (sel (next i)) = 0 :=
    (Finset.sum_eq_zero_iff.mp hz) i (Finset.mem_univ _)
  cases h : sel (next i)
  · simp [leave,hi,h] at hz'
  · rfl

lemma partial_boundary (next : Equiv.Perm V) (hc : IsCyclic next) (s : V → State)
    (ha : ∃ i, (s i).active = true) (hb : ∃ j, (s j).active = false) :
    2 ≤ B next s := by
  rw [boundary_eq_twice]
  suffices 0 < ∑ i, leave (s i).active (s (next i)).active by omega
  by_contra! hz
  have hz' : (∑ i, leave (s i).active (s (next i)).active) = 0 := Nat.eq_zero_of_le_zero hz
  obtain ⟨i,hi⟩ := ha
  obtain ⟨j,hj⟩ := hb
  obtain ⟨k,hk⟩ := hc i j
  have hi' : ∀ k : ℕ, (s ((next^k) i)).active = true := by
    intro k
    induction k with
    | zero => simpa using hi
    | succ k ih =>
      simpa [pow_succ',Equiv.Perm.mul_apply] using selected_of_no_leave next (fun i => (s i).active) hz' ih
  have := hi' k
  rw [hk,hj] at this
  cases this

/-- Source's four-unit error for a represented partial link of at most five
steps, derived from endpoint charging and actual cyclic transitions. -/
theorem dominant_partial_bound (next : Equiv.Perm V) (s : V → State) (line : V → Bool)
    (hcancel : ∀ i, ¬ (s i = dominant ∧ s (next i) = dominant))
    (hbip : ∀ i, s i = triangle → line i ≠ line (next i))
    (hcard : Fintype.card V ≤ 5) :
    2 * D s ≤ 2 * N s + Q s + P next s line + 4 := by
  exact (dominant_endpoint_bound next s line hcancel hbip).trans
    (Nat.add_le_add_left (boundary_le_four next s hcard) _)

lemma boundary_full (next : Equiv.Perm V) (s : V → State)
    (h : ∀ i, (s i).active = true) : B next s = 0 := by
  simp [B,boundary,h]

end FanLink
end HyperbolicObstruction
end
end

section

end
end

end OAI
