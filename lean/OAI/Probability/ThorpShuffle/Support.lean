import OAI.Probability.ThorpShuffle.Walsh

namespace OAI

universe uΩ uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

theorem fairMass_nonneg {Ω : Type uΩ} {α : Type uα} [Fintype Ω] (f : Ω → α) (a : α) :
    0 ≤ fairMass f a := by
  classical
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
    (Nat.cast_nonneg _)

theorem fairMass_sum {Ω : Type uΩ} {α : Type uα} [Fintype Ω] [Nonempty Ω] [Fintype α]
    (f : Ω → α) : ∑ a, fairMass f a = 1 := by
  classical
  unfold fairMass
  rw [← Finset.sum_div, Finset.sum_comm]
  simp [Fintype.card_ne_zero]

theorem sum_sub_le_tv {α : Type uα} [Fintype α] [DecidableEq α]
    (μ ν : α → ℝ) (hm : ∑ a, μ a = ∑ a, ν a) (s : Finset α) :
    (∑ a ∈ s, (μ a - ν a)) ≤ tv μ ν := by
  have h0 : ∑ a, (μ a - ν a) = 0 := by rw [Finset.sum_sub_distrib, hm, sub_self]
  have hsplit := s.sum_add_sum_compl (fun a => μ a - ν a)
  have hsplitabs := s.sum_add_sum_compl (fun a => |μ a - ν a|)
  have h₁ : (∑ a ∈ s, (μ a - ν a)) ≤ ∑ a ∈ s, |μ a - ν a| :=
    Finset.sum_le_sum (fun a _ => le_abs_self (μ a - ν a))
  have h₂ : -(∑ a ∈ sᶜ, (μ a - ν a)) ≤ ∑ a ∈ sᶜ, |μ a - ν a| := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun a _ => neg_le_abs (μ a - ν a))
  unfold tv
  linarith

theorem fairMass_tv_lower {Ω : Type uΩ} {α : Type uα} [Fintype Ω] [Nonempty Ω]
    [Fintype α] [Nonempty α] (f : Ω → α) :
    1 - (Fintype.card Ω : ℝ) / Fintype.card α ≤ tv (fairMass f)
      (fun _ => 1 / Fintype.card α) := by
  classical
  let s : Finset α := Finset.univ.image f
  have hm : ∑ a, fairMass f a = ∑ a : α, (1 / Fintype.card α : ℝ) := by
    rw [fairMass_sum]
    simp [Fintype.card_ne_zero]
  have hz (a : α) (ha : a ∉ s) : fairMass f a = 0 := by
    unfold fairMass
    have hne (ω : Ω) : f ω ≠ a := by
      intro h
      apply ha
      exact Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, h⟩
    simp [hne]
  have hs : ∑ a ∈ s, fairMass f a = 1 := by
    rw [← fairMass_sum f]
    exact Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hz a ha)
  have hbound := sum_sub_le_tv (fairMass f) (fun _ => 1 / Fintype.card α) hm s
  rw [Finset.sum_sub_distrib, hs] at hbound
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div] at hbound
  have hc : (s.card : ℝ) ≤ Fintype.card Ω := by
    exact_mod_cast (Finset.card_image_le (s := Finset.univ) (f := f))
  have hd : 0 ≤ (Fintype.card α : ℝ) := Nat.cast_nonneg _
  have hdiv := div_le_div_of_nonneg_right hc hd
  linarith

@[simp] theorem card_position (d : ℕ) : Fintype.card (Position d) = 2 ^ d := by
  simp [Position]

@[simp] theorem card_state (d : ℕ) : Fintype.card (State d) = (2 ^ d).factorial := by
  classical
  rw [Fintype.card_perm, card_position]

@[simp] theorem card_coins_succ (d : ℕ) : Fintype.card (Coins (d + 1)) = 2 ^ (2 ^ d) := by
  simp [Coins]

@[simp] theorem card_history_succ (d t : ℕ) :
    Fintype.card (History (d + 1) t) = 2 ^ (2 ^ d * t) := by
  simp [History, ← pow_mul]

theorem distance_support_lower (d t : ℕ) :
    1 - (2 : ℝ) ^ (2 ^ d * t) / ((2 ^ (d + 1)).factorial : ℝ) ≤
      distance (d + 1) t := by
  let : Nonempty (State (d + 1)) := ⟨Equiv.refl _⟩
  have h := fairMass_tv_lower (run (d + 1) t)
  change 1 - _ / _ ≤ tv (fairMass (run (d + 1) t))
    (fun _ => 1 / Fintype.card (State (d + 1)))
  simpa only [card_history_succ, card_state, Nat.cast_pow, Nat.cast_ofNat] using h

theorem worst_start_eq (d t : ℕ) (g₀ : State d) :
    tv (lawFrom d t g₀) (uniform d) = distance d t := by
  classical
  have hmass (g : State d) : lawFrom d t g₀ (g * g₀) = law d t g := by
    unfold lawFrom law fairMass
    congr 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : run d t ω = g <;> simp [h]
  unfold tv distance
  congr 1
  have h := Equiv.sum_comp (Equiv.mulRight g₀)
    (fun g : State d => |lawFrom d t g₀ g - uniform d g|)
  change (∑ g, |lawFrom d t g₀ (g * g₀) - (1 / Fintype.card (State d) : ℝ)|) = _ at h
  simp only [hmass] at h
  exact h.symm

theorem supportThreshold_le_of_distance {d t : ℕ} (hd : 1 ≤ d)
    (ht : distance d t ≤ 1 / 4) : supportThreshold d ≤ (t : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hfact : (0 : ℝ) < ((2 ^ (k + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hlower := distance_support_lower k t
  have hdiv : (3 : ℝ) / 4 ≤ 2 ^ (2 ^ k * t) / ((2 ^ (k + 1)).factorial : ℝ) := by
    linarith
  have hpow : 3 * ((2 ^ (k + 1)).factorial : ℝ) / 4 ≤ (2 : ℝ) ^ (2 ^ k * t) := by
    have h := (le_div_iff₀ hfact).mp hdiv
    nlinarith
  have hlog := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 3 * ((2 ^ (k + 1)).factorial : ℝ) / 4)
    (by positivity : (0 : ℝ) < 2 ^ (2 ^ k * t))).mpr hpow
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog
  simp only [mul_one] at hlog
  unfold supportThreshold
  apply Int.ceil_le.mpr
  push_cast
  have hden : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have hscale := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 2 / 2 ^ (k + 1))
  have hid : (2 / (2 : ℝ) ^ (k + 1)) * ((2 ^ k * t : ℕ) : ℝ) = t := by
    push_cast
    rw [pow_succ]
    field_simp
  rwa [hid] at hscale

theorem supportThreshold_le_mixingTime {d : ℕ} (hd : 1 ≤ d)
    (hex : ∃ t, distance d t ≤ 1 / 4) : supportThreshold d ≤ (mixingTime d : ℤ) := by
  apply supportThreshold_le_of_distance hd
  exact Nat.sInf_mem hex

end Thorp

end

end OAI
