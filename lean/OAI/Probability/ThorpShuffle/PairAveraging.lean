import OAI.Probability.ThorpShuffle.Model

namespace OAI

universe uΩ uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def mean {Ω : Type uΩ} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

def sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

@[simp] theorem sign_mul_self (b : Bool) : sign b * sign b = 1 := by
  simpa only [pow_two] using sign_sq b

def toggleCoin {α : Type uα} [DecidableEq α] (i : α) : Equiv.Perm (α → Bool) :=
  Function.Involutive.toPerm (fun c => Function.update c i (!(c i))) (by
    intro c
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h])

@[simp] theorem toggleCoin_apply {α : Type uα} [DecidableEq α]
    (i : α) (c : α → Bool) (j : α) :
    toggleCoin i c j = Function.update c i (!(c i)) j := rfl

theorem sum_sign {α : Type uα} [Fintype α] [DecidableEq α] (i : α) :
    ∑ c : α → Bool, sign (c i) = 0 := by
  have h := Equiv.sum_comp (toggleCoin i) (fun c : α → Bool => sign (c i))
  simp only [toggleCoin_apply, Function.update_self, sign_not, Finset.sum_neg_distrib] at h
  linarith

theorem sum_sign_pair {α : Type uα} [Fintype α] [DecidableEq α] (i j : α) :
    (∑ c : α → Bool, sign (c i) * sign (c j)) =
      if i = j then (Fintype.card (α → Bool) : ℝ) else 0 := by
  by_cases h : i = j
  · subst j
    simp
  · have he := Equiv.sum_comp (toggleCoin i) (fun c : α → Bool => sign (c i) * sign (c j))
    simp only [toggleCoin_apply, Function.update_self,
      Function.update_of_ne (Ne.symm h), sign_not, neg_mul,
      Finset.sum_neg_distrib] at he
    rw [ite_eq_right h]
    linarith

theorem mean_signed_sum_sq {α : Type uα} [Fintype α] [DecidableEq α] (a : α → ℝ) :
    mean (fun c : α → Bool => (∑ i, sign (c i) * a i) ^ 2) = ∑ i, a i ^ 2 := by
  have hs :
      (∑ c : α → Bool, (∑ i, sign (c i) * a i) ^ 2) =
        (Fintype.card (α → Bool) : ℝ) * ∑ i, a i ^ 2 := by
    calc
      _ = ∑ c : α → Bool, ∑ i, ∑ j,
          (sign (c i) * sign (c j)) * (a i * a j) := by
        apply Finset.sum_congr rfl
        intro c _
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i, ∑ j, (∑ c : α → Bool, sign (c i) * sign (c j)) * (a i * a j) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = _ := by
        simp only [sum_sign_pair, ite_mul, zero_mul]
        simp [Finset.mul_sum, pow_two]
  unfold mean
  rw [hs]
  have hcard : (Fintype.card (α → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ _ hcard

def pairUpdate (free₀ free₁ : Bool) (a b : ℝ) (coin : Bool) : ℝ × ℝ :=
  if free₀ && free₁ then ((a + b) / 2, (a + b) / 2)
  else if coin then (b, a) else (a, b)

@[simp] theorem pairUpdate_sum (free₀ free₁ : Bool) (a b : ℝ) (coin : Bool) :
    (pairUpdate free₀ free₁ a b coin).1 + (pairUpdate free₀ free₁ a b coin).2 = a + b := by
  cases free₀ <;> cases free₁ <;> cases coin <;> simp [pairUpdate] <;> ring

theorem pairUpdate_difference (free₀ free₁ : Bool) (a b : ℝ) (coin : Bool) :
    (pairUpdate free₀ free₁ a b coin).1 - (pairUpdate free₀ free₁ a b coin).2 =
      sign coin * (if free₀ && free₁ then 0 else a - b) := by
  cases free₀ <;> cases free₁ <;> cases coin <;> simp [pairUpdate, sign]

theorem pairUpdate_mean_first (free₀ free₁ : Bool) (a b : ℝ) :
    mean (fun coin : Bool => (pairUpdate free₀ free₁ a b coin).1) = (a + b) / 2 := by
  cases free₀ <;> cases free₁ <;> simp [mean, pairUpdate] <;> ring

theorem pairUpdate_difference_sq (free₀ free₁ : Bool) (a b : ℝ)
    (ha : free₀ = false → a = 0) (hb : free₁ = false → b = 0) :
    (if free₀ && free₁ then (0 : ℝ) else a - b) ^ 2 =
      (if free₁ then 0 else a ^ 2) + (if free₀ then 0 else b ^ 2) := by
  cases free₀ <;> cases free₁ <;> simp_all

def flow {α : Type uα} (B : Bool × α → Bool) (w : Bool × α → ℝ)
    (c : α → Bool) (x : Bool × α) : ℝ :=
  let p := pairUpdate (B (false, x.2)) (B (true, x.2))
    (w (false, x.2)) (w (true, x.2)) (c x.2)
  if x.1 then p.2 else p.1

def oddCoefficient {α : Type uα} [Fintype α] (ε : α → ℝ) (w : Bool × α → ℝ) : ℝ :=
  ∑ i, ε i * (w (false, i) - w (true, i))

theorem mean_oddCoefficient_sq {α : Type uα} [Fintype α] [DecidableEq α]
    (B : Bool × α → Bool) (w : Bool × α → ℝ) (ε : α → ℝ)
    (hw : ∀ x, B x = false → w x = 0) (hε : ∀ i, ε i ^ 2 = 1) :
    mean (fun c : α → Bool => oddCoefficient ε (flow B w c) ^ 2) =
      ∑ i, ((if B (true, i) then 0 else w (false, i) ^ 2) +
        (if B (false, i) then 0 else w (true, i) ^ 2)) := by
  have he (c : α → Bool) :
      oddCoefficient ε (flow B w c) =
        ∑ i, sign (c i) * (ε i *
          (if B (false, i) && B (true, i) then 0 else w (false, i) - w (true, i))) := by
    unfold oddCoefficient
    apply Finset.sum_congr rfl
    intro i _
    simp only [flow, Bool.false_eq_true, ↓reduceIte]
    rw [pairUpdate_difference]
    ring
  simp_rw [he]
  rw [mean_signed_sum_sq]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, hε, one_mul]
  exact pairUpdate_difference_sq _ _ _ _ (hw _) (hw _)

end Conditional

namespace Conditional

def pairMap {α : Type uα} (c : α → Bool) (x : Bool × α) : Bool × α :=
  (x.1 ^^ c x.2, x.2)

theorem pairMap_involutive {α : Type uα} (c : α → Bool) :
    Function.Involutive (pairMap c) := by
  rintro ⟨b, i⟩
  cases b <;> cases h : c i <;> simp [pairMap, h]

theorem flow_sub {α : Type uα} (B : Bool × α → Bool) (u v : Bool × α → ℝ)
    (c : α → Bool) (x : Bool × α) :
    flow B (fun y => u y - v y) c x = flow B u c x - flow B v c x := by
  rcases x with ⟨b, i⟩
  cases b <;> cases h₀ : B (false, i) <;> cases h₁ : B (true, i) <;>
    cases hc : c i <;> simp [flow, pairUpdate, h₀, h₁, hc] <;> ring

theorem flow_uniform {α : Type uα} (B : Bool × α → Bool) (r : ℝ)
    (c : α → Bool) (x : Bool × α) :
    flow B (fun y => if B y then r else 0) c x =
      if B (pairMap c x) then r else 0 := by
  rcases x with ⟨b, i⟩
  cases b <;> cases h₀ : B (false, i) <;> cases h₁ : B (true, i) <;>
    cases hc : c i <;> simp [flow, pairUpdate, pairMap, h₀, h₁, hc]

theorem flow_support {α : Type uα} (B : Bool × α → Bool) (w : Bool × α → ℝ)
    (hw : ∀ x, B x = false → w x = 0) (c : α → Bool) (x : Bool × α)
    (hx : B (pairMap c x) = false) : flow B w c x = 0 := by
  rcases x with ⟨b, i⟩
  have h₀ := hw (false, i)
  have h₁ := hw (true, i)
  cases b <;> cases hb₀ : B (false, i) <;> cases hb₁ : B (true, i) <;>
    cases hc : c i <;> simp_all [flow, pairUpdate, pairMap]

theorem flow_evenCoefficient {α : Type uα} [Fintype α]
    (B : Bool × α → Bool) (w : Bool × α → ℝ) (ε : α → ℝ) (c : α → Bool) :
    (∑ i, ε i * (flow B w c (false, i) + flow B w c (true, i))) =
      ∑ i, ε i * (w (false, i) + w (true, i)) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [flow, Bool.false_eq_true, ↓reduceIte, pairUpdate_sum]

theorem flow_sum {α : Type uα} [Fintype α] (B : Bool × α → Bool)
    (w : Bool × α → ℝ) (c : α → Bool) :
    (∑ x, flow B w c x) = ∑ x, w x := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [flow, Bool.false_eq_true, ↓reduceIte, add_comm] using
    (pairUpdate_sum (B (false, i)) (B (true, i)) (w (false, i)) (w (true, i)) (c i))

theorem pairUpdate_energy_le (free₀ free₁ : Bool) (a b : ℝ) (coin : Bool) :
    (pairUpdate free₀ free₁ a b coin).1 ^ 2 +
        (pairUpdate free₀ free₁ a b coin).2 ^ 2 ≤ a ^ 2 + b ^ 2 := by
  have h := sq_nonneg (a - b)
  cases free₀ <;> cases free₁ <;> cases coin <;> simp [pairUpdate] <;> nlinarith

theorem flow_energy_le {α : Type uα} [Fintype α] (B : Bool × α → Bool)
    (w : Bool × α → ℝ) (c : α → Bool) :
    (∑ x, flow B w c x ^ 2) ≤ ∑ x, w x ^ 2 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [flow, Bool.false_eq_true, ↓reduceIte, add_comm] using
    pairUpdate_energy_le (B (false, i)) (B (true, i)) (w (false, i)) (w (true, i)) (c i)

theorem pairUpdate_first_noise (free₀ free₁ : Bool) (a b : ℝ) (coin : Bool) :
    (pairUpdate free₀ free₁ a b coin).1 = (a + b) / 2 +
      sign coin * (if free₀ && free₁ then 0 else (a - b) / 2) := by
  cases free₀ <;> cases free₁ <;> cases coin <;> simp [pairUpdate, sign] <;> ring

theorem pairUpdate_second_noise (free₀ free₁ : Bool) (a b : ℝ) (coin : Bool) :
    (pairUpdate free₀ free₁ a b coin).2 = (a + b) / 2 -
      sign coin * (if free₀ && free₁ then 0 else (a - b) / 2) := by
  cases free₀ <;> cases free₁ <;> cases coin <;> simp [pairUpdate, sign] <;> ring

end Conditional

end Thorp

end

end OAI
