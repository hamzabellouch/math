import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PermutationPaths

theorem path_squared_difference_le {α : Type*} [Fintype α]
    (f : α → ℝ) (p : ℕ → α → α) (N : ℕ) :
    (∑ x, (f (p 0 x) - f (p N x)) ^ 2) ≤
      (N : ℝ) * ∑ i ∈ Finset.range N,
        ∑ x, (f (p i x) - f (p (i + 1) x)) ^ 2 := by
  have hpoint (x : α) : (f (p 0 x) - f (p N x)) ^ 2 ≤
      (N : ℝ) * ∑ i ∈ Finset.range N,
        (f (p i x) - f (p (i + 1) x)) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range N)
      (f := fun i => f (p i x) - f (p (i + 1) x))
    simpa only [Finset.sum_range_sub', Finset.card_range] using h
  calc
    (∑ x, (f (p 0 x) - f (p N x)) ^ 2)
        ≤ ∑ x, (N : ℝ) * ∑ i ∈ Finset.range N,
            (f (p i x) - f (p (i + 1) x)) ^ 2 :=
      Finset.sum_le_sum fun x _ => hpoint x
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

theorem permutation_path_energy_le {α : Type*} [Fintype α]
    (f : α → ℝ) (S : Finset (Equiv.Perm α))
    (p : ℕ → Equiv.Perm α) (N : ℕ)
    (hstep : ∀ i < N, ∃ s ∈ S, p (i + 1) = s * p i) :
    (∑ x, (f (p 0 x) - f (p N x)) ^ 2) ≤
      (N : ℝ) ^ 2 * ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2 := by
  classical
  let B : ℝ := ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2
  have hone (i : ℕ) (hi : i ∈ Finset.range N) :
      (∑ x, (f (p i x) - f (p (i + 1) x)) ^ 2) ≤ B := by
    obtain ⟨s, hs, hsi⟩ := hstep i (Finset.mem_range.mp hi)
    calc
      (∑ x, (f (p i x) - f (p (i + 1) x)) ^ 2)
          = ∑ x, (f x - f (s x)) ^ 2 := by
        apply Fintype.sum_equiv (p i)
        intro x
        rw [hsi, Equiv.Perm.mul_apply]
      _ ≤ B := by
        dsimp [B]
        exact Finset.single_le_sum
          (fun t _ => show 0 ≤ ∑ x, (f x - f (t x)) ^ 2 from
            Finset.sum_nonneg fun x _ => sq_nonneg _) hs
  calc
    (∑ x, (f (p 0 x) - f (p N x)) ^ 2)
        ≤ (N : ℝ) * ∑ i ∈ Finset.range N,
          ∑ x, (f (p i x) - f (p (i + 1) x)) ^ 2 :=
      path_squared_difference_le f (fun i => p i) N
    _ ≤ (N : ℝ) * ∑ _i ∈ Finset.range N, B := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hone) (Nat.cast_nonneg _)
    _ = (N : ℝ) ^ 2 * ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [B]
      ring

theorem sum_group_apply_eq {α G : Type*} [Fintype α] [Nonempty α]
    [Group G] [Fintype G] (ρ : G →* Equiv.Perm α)
    (htrans : ∀ x y : α, ∃ g : G, ρ g x = y) (f : α → ℝ) (x : α) :
    (∑ g : G, f (ρ g x)) =
      (Fintype.card G : ℝ) / Fintype.card α * ∑ y, f y := by
  have hsame (y : α) : (∑ g : G, f (ρ g y)) = ∑ g : G, f (ρ g x) := by
    obtain ⟨h, rfl⟩ := htrans x y
    apply Fintype.sum_equiv (Equiv.mulRight h)
    intro g
    simp [map_mul, Equiv.Perm.mul_apply]
  have hsum (g : G) : (∑ y, f (ρ g y)) = ∑ y, f y := by
    exact Fintype.sum_equiv (ρ g) _ _ (fun _ => rfl)
  have hid : (Fintype.card α : ℝ) * (∑ g : G, f (ρ g x)) =
      (Fintype.card G : ℝ) * ∑ y, f y := by
    calc
      (Fintype.card α : ℝ) * (∑ g : G, f (ρ g x))
          = ∑ y : α, ∑ g : G, f (ρ g y) := by simp [hsame]
      _ = ∑ g : G, ∑ y : α, f (ρ g y) := Finset.sum_comm
      _ = _ := by simp [hsum]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hc).2
  simpa [mul_comm] using hid

theorem sum_pairwise_sq_eq {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) :
    (∑ x, ∑ y, (f x - f y) ^ 2) =
      2 * (Fintype.card α : ℝ) *
        ∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2 := by
  let μ : ℝ := (∑ y, f y) / Fintype.card α
  have hc : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcenter : (∑ x, (f x - μ)) = 0 := by
    simp [μ, Finset.sum_sub_distrib, hc, mul_div_cancel₀]
  change _ = 2 * (Fintype.card α : ℝ) * ∑ x, (f x - μ) ^ 2
  calc
    (∑ x, ∑ y, (f x - f y) ^ 2) =
        ∑ x, ∑ y, ((f x - μ) ^ 2 + (f y - μ) ^ 2 -
          2 * (f x - μ) * (f y - μ)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcenter]
      simp only [mul_zero, Finset.sum_const_zero, sub_zero, Finset.card_univ]
      rw [← Finset.mul_sum]
      ring

theorem sum_group_squared_difference_eq {α G : Type*} [Fintype α] [Nonempty α]
    [Group G] [Fintype G] (ρ : G →* Equiv.Perm α)
    (htrans : ∀ x y : α, ∃ g : G, ρ g x = y) (f : α → ℝ) :
    (∑ g : G, ∑ x, (f x - f (ρ g x)) ^ 2) =
      2 * (Fintype.card G : ℝ) *
        ∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2 := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    (∑ g : G, ∑ x, (f x - f (ρ g x)) ^ 2)
        = ∑ x, ∑ g : G, (f x - f (ρ g x)) ^ 2 := Finset.sum_comm
    _ = ∑ x, (Fintype.card G : ℝ) / Fintype.card α *
        ∑ y, (f x - f y) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      exact sum_group_apply_eq ρ htrans (fun y => (f x - f y) ^ 2) x
    _ = (Fintype.card G : ℝ) / Fintype.card α *
        (∑ x, ∑ y, (f x - f y) ^ 2) := (Finset.mul_sum _ _ _).symm
    _ = _ := by
      rw [sum_pairwise_sq_eq f]
      field_simp

theorem variance_le_generator_energy {α G : Type*} [Fintype α] [Nonempty α]
    [Group G] [Fintype G] (ρ : G →* Equiv.Perm α)
    (htrans : ∀ x y : α, ∃ g : G, ρ g x = y)
    (S : Finset (Equiv.Perm α)) (N : ℕ)
    (hpaths : ∀ g : G, ∃ (p : ℕ → Equiv.Perm α) (L : ℕ),
      L ≤ N ∧ p 0 = 1 ∧ p L = ρ g ∧
        ∀ i < L, ∃ s ∈ S, p (i + 1) = s * p i)
    (f : α → ℝ) :
    (∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2) ≤
      (N : ℝ) ^ 2 / 2 * ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2 := by
  classical
  let B : ℝ := ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2
  have hB : 0 ≤ B := Finset.sum_nonneg fun s _ =>
    Finset.sum_nonneg fun x _ => sq_nonneg _
  have hbound (g : G) : (∑ x, (f x - f (ρ g x)) ^ 2) ≤ (N : ℝ) ^ 2 * B := by
    obtain ⟨p, L, hLN, hzero, hend, hstep⟩ := hpaths g
    have hpath := permutation_path_energy_le f S p L hstep
    simp only [hzero, hend, Equiv.Perm.one_apply] at hpath
    calc
      (∑ x, (f x - f (ρ g x)) ^ 2) ≤ (L : ℝ) ^ 2 * B := hpath
      _ ≤ (N : ℝ) ^ 2 * B := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg L) (by exact_mod_cast hLN) 2) hB
  have hsum : 2 * (Fintype.card G : ℝ) *
      (∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2) ≤
      (Fintype.card G : ℝ) * ((N : ℝ) ^ 2 * B) := by
    rw [← sum_group_squared_difference_eq ρ htrans f]
    calc
      _ ≤ ∑ _g : G, (N : ℝ) ^ 2 * B := Finset.sum_le_sum fun g _ => hbound g
      _ = _ := by simp
  have hG : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcancel : 2 * (∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2) ≤
      (N : ℝ) ^ 2 * B := by
    apply (mul_le_mul_iff_right₀ hG).mp
    nlinarith [hsum]
  change _ ≤ (N : ℝ) ^ 2 / 2 * B
  linarith

theorem exists_path_of_word {α : Type*} (S : Finset (Equiv.Perm α))
    (l : List (Equiv.Perm α)) (hl : ∀ s ∈ l, s ∈ S) :
    ∃ p : ℕ → Equiv.Perm α, p 0 = 1 ∧ p l.length = l.prod ∧
      ∀ i < l.length, ∃ s ∈ S, p (i + 1) = s * p i := by
  classical
  induction l with
  | nil =>
      exact ⟨fun _ => 1, rfl, rfl, by simp⟩
  | cons s l ih =>
      obtain ⟨p, hp0, hpend, hpstep⟩ := ih (fun t ht => hl t (List.mem_cons_of_mem s ht))
      let q : ℕ → Equiv.Perm α := fun i => if i ≤ l.length then p i else s * p l.length
      refine ⟨q, ?_, ?_, ?_⟩
      · simp [q, hp0]
      · simp [q, hpend]
      · intro i hi
        simp only [List.length_cons] at hi
        by_cases hil : i < l.length
        · obtain ⟨t, ht, hti⟩ := hpstep i hil
          refine ⟨t, ht, ?_⟩
          simpa [q, Nat.le_of_lt hil, Nat.succ_le_of_lt hil] using hti
        · have hieq : i = l.length := by omega
          subst i
          refine ⟨s, hl s (List.mem_cons_self ..), ?_⟩
          simp [q]

theorem variance_le_generator_energy_of_words {α G : Type*}
    [Fintype α] [Nonempty α] [Group G] [Fintype G]
    (ρ : G →* Equiv.Perm α)
    (htrans : ∀ x y : α, ∃ g : G, ρ g x = y)
    (S : Finset (Equiv.Perm α)) (N : ℕ)
    (hwords : ∀ g : G, ∃ l : List (Equiv.Perm α),
      l.length ≤ N ∧ l.prod = ρ g ∧ ∀ s ∈ l, s ∈ S)
    (f : α → ℝ) :
    (∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2) ≤
      (N : ℝ) ^ 2 / 2 * ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2 := by
  apply variance_le_generator_energy ρ htrans S N ?_ f
  intro g
  obtain ⟨l, hlength, hprod, hletters⟩ := hwords g
  obtain ⟨p, hp0, hpend, hpstep⟩ := exists_path_of_word S l hletters
  exact ⟨p, l.length, hlength, hp0, hpend.trans hprod, hpstep⟩

end Problem315.PermutationPaths

end

end OAI
