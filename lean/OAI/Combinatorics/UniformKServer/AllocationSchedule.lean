import Mathlib

namespace OAI

                                         
section

/-! Exact coarse held-size schedule in companion §03. The deterministic
potential below pays relative refreshes and both hysteretic on/off transitions
from variation of the underlying persistent rank estimates. In particular it
does not restart any initialization allowance when a child becomes active. -/
namespace UniformKServer.AllocationSchedule
noncomputable section
open Finset

def compared (δ b x : ℝ) : Prop := x ≤ (1+δ)*b ∧ b ≤ (1+δ)*x

def relativeUpdate (δ b x : ℝ) : ℝ := by
  classical
  exact if compared δ b x then b else x

def size : Option ℝ → ℝ
  | none => 0
  | some b => b

def update (c δ : ℝ) (s : Option ℝ) (x : ℝ) : Option ℝ :=
  match s with
  | none => if 5*c ≤ x then some x else none
  | some b => if x ≤ 2*c then none else some (relativeUpdate δ b x)

def charge (a b : ℝ) : ℝ := if a=b then 0 else a+b

def potential (K c x : ℝ) (s : Option ℝ) : ℝ :=
  K*|x-size s| + match s with | none => 0 | some _ => 2*(K+1)*c

theorem charge_self (a : ℝ) : charge a a=0 := by simp [charge]

theorem charge_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : charge a b ≤ a+b := by
  unfold charge
  split
  · linarith
  · rfl

theorem failure_cost {δ b x K : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hK : 1+2/δ ≤ K) (hf : ¬compared δ b x) : b+x ≤ K*|x-b| := by
  have hd : 2 ≤ (K-1)*δ := (div_le_iff₀ hδ).mp (by linarith : 2/δ ≤ K-1)
  have hK' : δ+2 ≤ K*δ := by nlinarith
  unfold compared at hf
  push Not at hf
  by_cases h : x ≤ (1+δ)*b
  · have h' := hf h
    have hbx : x ≤ b := by nlinarith
    rw [abs_of_nonpos (by linarith)]
    have hgap : δ*x ≤ b-x := by nlinarith
    have hbound := mul_le_mul_of_nonneg_right hK' (sub_nonneg.mpr hbx)
    have hδb : δ*(b+x) ≤ (δ+2)*(b-x) := by nlinarith
    nlinarith
  · have h' : (1+δ)*b < x := lt_of_not_ge h
    have hbx : b ≤ x := by nlinarith
    rw [abs_of_nonneg (by linarith)]
    have hbound := mul_le_mul_of_nonneg_right hK' (sub_nonneg.mpr hbx)
    have hδb : δ*(b+x) ≤ (δ+2)*(x-b) := by nlinarith
    nlinarith

theorem relative_nonneg {δ b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) :
    0 ≤ relativeUpdate δ b x := by unfold relativeUpdate; split <;> assumption

theorem relative_compared {δ b x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) :
    compared δ (relativeUpdate δ b x) x := by
  unfold relativeUpdate
  split
  · assumption
  · constructor <;> nlinarith

theorem relative_drop {δ b x K : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hK : 1+2/δ ≤ K) :
    charge b (relativeUpdate δ b x)+K*|x-relativeUpdate δ b x| ≤ K*|x-b| := by
  unfold relativeUpdate
  split
  · rw [charge_self,zero_add]
  · rename_i hf
    rw [sub_self,abs_zero,mul_zero,add_zero]
    exact (charge_le hb hx).trans (failure_cost hδ hb hx hK hf)

theorem update_nonneg {c δ : ℝ} (s : Option ℝ) {x : ℝ}
    (hs : 0 ≤ size s) (hx : 0 ≤ x) : 0 ≤ size (update c δ s x) := by
  cases s with
  | none =>
    simp only [update]
    split
    · exact hx
    · exact le_refl _
  | some b =>
    simp only [update]
    split
    · simp [size]
    · exact relative_nonneg hs hx

theorem potential_nonneg {K c x : ℝ} (s : Option ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c) :
    0 ≤ potential K c x s := by
  cases s <;> dsimp [potential] <;> positivity

theorem update_drop {c δ K : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hK : 3 ≤ K) (hKδ : 1+2/δ ≤ K) (s : Option ℝ) {x : ℝ}
    (hs : 0 ≤ size s) (hx : 0 ≤ x) :
    charge (size s) (size (update c δ s x))+potential K c x (update c δ s x) ≤
      potential K c x s := by
  cases s with
  | none =>
    simp only [update]
    split
    · rename_i hxhigh
      have hch : charge 0 x ≤ x := by simpa using charge_le (le_refl (0:ℝ)) hx
      simp only [size,potential,sub_self,abs_zero,mul_zero,zero_add,sub_zero,abs_of_nonneg hx,add_zero]
      have hm := mul_nonneg (by linarith : 0 ≤ K-1) (by linarith : 0 ≤ x-5*c)
      have hh := mul_nonneg (by linarith : 0 ≤ 3*K-7) hc
      nlinarith
    · simp only [size,charge_self,potential,zero_add]
      exact le_rfl
  | some b =>
    have hb : 0 ≤ b := hs
    simp only [update]
    split
    · rename_i hxlow
      have hch : charge b 0 ≤ b := by simpa using charge_le hb (le_refl (0:ℝ))
      simp only [size,potential,sub_zero,abs_of_nonneg hx,add_zero]
      have htri : b ≤ |x-b|+x := by linarith [neg_le_abs (x-b)]
      have hm := mul_nonneg (by linarith : 0 ≤ K-1) (abs_nonneg (x-b))
      have hh := mul_le_mul_of_nonneg_left hxlow (by linarith : 0 ≤ K+1)
      linarith
    · simp only [size,potential]
      linarith [relative_drop hδ hb hx hKδ]

theorem potential_change {K c x y : ℝ} (s : Option ℝ) (hK : 0 ≤ K) :
    potential K c y s ≤ potential K c x s+K*|y-x| := by
  have ht : |y-size s| ≤ |x-size s|+|y-x| := by
    convert abs_add_le (x-size s) (y-x) using 1
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_left ht hK
  unfold potential
  linarith

theorem update_step {c δ K : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hK : 3 ≤ K) (hKδ : 1+2/δ ≤ K) (s : Option ℝ) {x y : ℝ}
    (hs : 0 ≤ size s) (hy : 0 ≤ y) :
    charge (size s) (size (update c δ s y))+potential K c y (update c δ s y) ≤
      potential K c x s+K*|y-x| :=
  (update_drop hc hδ hK hKδ s hs hy).trans (potential_change s (by linarith))

def schedule (c δ : ℝ) (x : ℕ → ℝ) : ℕ → Option ℝ
  | 0 => update c δ none (x 0)
  | t+1 => update c δ (schedule c δ x t) (x (t+1))

theorem schedule_nonneg {c δ : ℝ} {x : ℕ → ℝ} (hx : ∀ t, 0 ≤ x t) :
    ∀ t, 0 ≤ size (schedule c δ x t) := by
  intro t
  induction t with
  | zero => exact update_nonneg none (le_refl _) (hx 0)
  | succ t ih => exact update_nonneg _ ih (hx (t+1))

theorem schedule_budget {c δ K : ℝ} {x : ℕ → ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hK : 3 ≤ K) (hKδ : 1+2/δ ≤ K) (hx : ∀ t, 0 ≤ x t) (H : ℕ) :
    (∑ t ∈ range H, charge (size (schedule c δ x t)) (size (schedule c δ x (t+1)))) ≤
      K*(∑ t ∈ range H, |x (t+1)-x t|)+potential K c (x 0) (schedule c δ x 0) := by
  have hsum : ∀ H,
      (∑ t ∈ range H, charge (size (schedule c δ x t)) (size (schedule c δ x (t+1)))) +
        potential K c (x H) (schedule c δ x H) ≤
      K*(∑ t ∈ range H, |x (t+1)-x t|)+potential K c (x 0) (schedule c δ x 0) := by
    intro H
    induction H with
    | zero => simp
    | succ H ih =>
      rw [sum_range_succ,sum_range_succ]
      have ht := update_step hc hδ hK hKδ (schedule c δ x H) (x:=x H)
        (schedule_nonneg hx H) (hx (H+1))
      change charge (size (schedule c δ x H)) (size (schedule c δ x (H+1))) +
        potential K c (x (H+1)) (schedule c δ x (H+1)) ≤
        potential K c (x H) (schedule c δ x H)+K*|x (H+1)-x H| at ht
      nlinarith
  have hp := potential_nonneg (schedule c δ x H) (by linarith : 0 ≤ K) hc (x:=x H)
  linarith [hsum H]

/-- A single relative-held reference, used for the parent and for one side epoch. -/
def held (δ : ℝ) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | t+1 => relativeUpdate δ (held δ x t) (x (t+1))

theorem held_nonneg {δ : ℝ} {x : ℕ → ℝ} (hx : ∀ t, 0 ≤ x t) :
    ∀ t, 0 ≤ held δ x t := by
  intro t
  induction t with
  | zero => exact hx 0
  | succ t ih => exact relative_nonneg ih (hx (t+1))

theorem held_compared {δ : ℝ} {x : ℕ → ℝ} (hδ : 0 ≤ δ) (hx : ∀ t, 0 ≤ x t)
    (t : ℕ) : compared δ (held δ x t) (x t) := by
  cases t with
  | zero => constructor <;> dsimp [held] <;> nlinarith [hx 0]
  | succ t => exact relative_compared hδ (hx (t+1))

theorem relative_step {δ K x y b : ℝ} (hδ : 0 < δ) (hK : 1+2/δ ≤ K)
    (hb : 0 ≤ b) (hy : 0 ≤ y) :
    charge b (relativeUpdate δ b y)+K*|y-relativeUpdate δ b y| ≤
      K*|x-b|+K*|y-x| := by
  have hKpos : 0 ≤ K := by have := div_pos (by norm_num : (0:ℝ)<2) hδ; linarith
  have htri : |y-b| ≤ |x-b|+|y-x| := by
    convert abs_add_le (x-b) (y-x) using 1
    congr 1
    ring
  exact (relative_drop hδ hb hy hK).trans (by nlinarith [mul_le_mul_of_nonneg_left htri hKpos])

theorem held_budget {δ K : ℝ} {x : ℕ → ℝ} (hδ : 0 < δ)
    (hK : 1+2/δ ≤ K) (hx : ∀ t, 0 ≤ x t) (H : ℕ) :
    (∑ t ∈ range H, charge (held δ x t) (held δ x (t+1))) ≤
      K*(∑ t ∈ range H, |x (t+1)-x t|) := by
  have hKpos : 0 ≤ K := by have := div_pos (by norm_num : (0:ℝ)<2) hδ; linarith
  have hsum : ∀ H,
      (∑ t ∈ range H, charge (held δ x t) (held δ x (t+1))) +
        K*|x H-held δ x H| ≤ K*(∑ t ∈ range H, |x (t+1)-x t|) := by
    intro H
    induction H with
    | zero => simp [held]
    | succ H ih =>
      rw [sum_range_succ,sum_range_succ]
      have ht := relative_step (x:=x H) hδ hK (held_nonneg (δ:=δ) hx H) (hx (H+1))
      change charge (held δ x H) (held δ x (H+1)) + K*|x (H+1)-held δ x (H+1)| ≤
        K*|x H-held δ x H|+K*|x (H+1)-x H| at ht
      nlinarith
  nlinarith [hsum H,mul_nonneg hKpos (abs_nonneg (x H-held δ x H))]

theorem update_inactive {c δ x : ℝ} (hc : 0 ≤ c) (s : Option ℝ)
    (h : update c δ s x=none) : x ≤ 5*c := by
  cases s with
  | none =>
    simp only [update] at h
    split at h
    · contradiction
    · rename_i hx
      exact (lt_of_not_ge hx).le
  | some b =>
    simp only [update] at h
    split at h
    · linarith
    · contradiction

theorem update_active {c δ x b : ℝ} (_hc : 0 ≤ c) (hδ : 0 ≤ δ) (hx : 0 ≤ x)
    (s : Option ℝ) (h : update c δ s x=some b) :
    compared δ b x ∧ 2*c ≤ x := by
  cases s with
  | none =>
    simp only [update] at h
    split at h
    · have hxb : x=b := Option.some.inj h
      subst b
      constructor
      · constructor <;> nlinarith
      · linarith
    · contradiction
  | some a =>
    simp only [update] at h
    split at h
    · contradiction
    · have hab : relativeUpdate δ a x=b := Option.some.inj h
      subst b
      exact ⟨relative_compared hδ hx,by linarith⟩

theorem initial_potential_bound {c δ K x : ℝ} (hc : 0 ≤ c) (hK : 1 ≤ K)
    (hx : 0 ≤ x) : potential K c x (update c δ none x) ≤ 5*K*c := by
  simp only [update]
  split
  · simp only [potential,size,sub_self,abs_zero,mul_zero,zero_add]
    nlinarith
  · simp only [potential,size,sub_zero,abs_of_nonneg hx,add_zero]
    nlinarith

/-- Side charge uses actual totals, not the held values. -/
theorem side_charge {δ b x y : ℝ} (hδ : 0 ≤ δ) (hy : 0 ≤ y)
    (hcmp : compared δ b x) : x+y ≤ (1+δ)*(b+y) := by
  rcases hcmp with ⟨hx,_⟩
  nlinarith

end
end UniformKServer.AllocationSchedule

end

end OAI
