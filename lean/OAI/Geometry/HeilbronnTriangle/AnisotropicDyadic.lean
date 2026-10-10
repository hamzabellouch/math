import Mathlib

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem355.Anisotropic

theorem card_dyadic_indices_le (S : Finset ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ i ∈ S, (2 : ℝ) ^ i ≤ R) :
    (S.card : ℝ) ≤ Real.log (2 * R) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hquot : 0 ≤ Real.log R / Real.log 2 := div_nonneg hlogR hlog2.le
  have hi (i : ℕ) (hi : i ∈ S) : i ≤ ⌊Real.log R / Real.log 2⌋₊ := by
    apply Nat.le_floor
    apply (le_div_iff₀ hlog2).mpr
    calc
      (i : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ i) := (Real.log_pow 2 i).symm
      _ ≤ Real.log R := Real.log_le_log (by positivity) (hS i hi)
  have hs : S ⊆ Finset.range (⌊Real.log R / Real.log 2⌋₊ + 1) := by
    intro i hmem
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hi i hmem))
  have hc : (S.card : ℝ) ≤ (⌊Real.log R / Real.log 2⌋₊ : ℝ) + 1 := by
    exact_mod_cast (show S.card ≤ ⌊Real.log R / Real.log 2⌋₊ + 1 by
      simpa using Finset.card_le_card hs)
  calc
    (S.card : ℝ) ≤ (⌊Real.log R / Real.log 2⌋₊ : ℝ) + 1 := hc
    _ ≤ Real.log R / Real.log 2 + 1 := by
      linarith [Nat.floor_le hquot]
    _ = Real.log (2 * R) / Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by linarith : R ≠ 0)]
      field_simp
      ring

theorem card_dyadic_pairs_le (S : Finset (ℕ × ℕ)) {R T : ℝ}
    (hR : 1 ≤ R) (hT : 1 ≤ T)
    (hS : ∀ p ∈ S, (2 : ℝ) ^ p.1 ≤ R ∧ (2 : ℝ) ^ p.2 ≤ T) :
    (S.card : ℝ) ≤
      (Real.log (2 * R) / Real.log 2) * (Real.log (2 * T) / Real.log 2) := by
  have hfst : ∀ i ∈ S.image Prod.fst, (2 : ℝ) ^ i ≤ R := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact (hS p hp).1
  have hsnd : ∀ i ∈ S.image Prod.snd, (2 : ℝ) ^ i ≤ T := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact (hS p hp).2
  have hsub : S ⊆ (S.image Prod.fst) ×ˢ (S.image Prod.snd) := by
    intro p hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hc : (S.card : ℝ) ≤
      ((S.image Prod.fst).card : ℝ) * ((S.image Prod.snd).card : ℝ) := by
    exact_mod_cast (show S.card ≤ (S.image Prod.fst).card * (S.image Prod.snd).card by
      simpa using Finset.card_le_card hsub)
  exact hc.trans (mul_le_mul (card_dyadic_indices_le _ hR hfst)
    (card_dyadic_indices_le _ hT hsnd) (by positivity)
    ((Nat.cast_nonneg _).trans (card_dyadic_indices_le _ hR hfst)))

theorem sum_le_of_dyadic_fibers {α : Type*} [DecidableEq α]
    (S : Finset α) (index : α → ℕ × ℕ) (weight : α → ℝ)
    {R T A : ℝ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hA : 0 ≤ A)
    (hindex : ∀ x ∈ S, (2 : ℝ) ^ (index x).1 ≤ R ∧
      (2 : ℝ) ^ (index x).2 ≤ T)
    (hgroup : ∀ p ∈ S.image index,
      ∑ x ∈ S with index x = p, weight x ≤ A) :
    ∑ x ∈ S, weight x ≤
      A * (Real.log (2 * R) / Real.log 2) * (Real.log (2 * T) / Real.log 2) := by
  have hscales : ∀ p ∈ S.image index,
      (2 : ℝ) ^ p.1 ≤ R ∧ (2 : ℝ) ^ p.2 ≤ T := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact hindex x hx
  calc
    ∑ x ∈ S, weight x = ∑ p ∈ S.image index,
        ∑ x ∈ S with index x = p, weight x := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun x hx => Finset.mem_image_of_mem index hx) weight
    _ ≤ ∑ _p ∈ S.image index, A := Finset.sum_le_sum hgroup
    _ = A * ((S.image index).card : ℝ) := by simp [mul_comm]
    _ ≤ A * ((Real.log (2 * R) / Real.log 2) *
        (Real.log (2 * T) / Real.log 2)) :=
      mul_le_mul_of_nonneg_left (card_dyadic_pairs_le _ hR hT hscales) hA
    _ = _ := by ring

theorem thin_group_numeric {U Z R₁ R₂ R₃ C : ℝ}
    (hU : 0 < U) (hZ : 0 < Z) (hR : 0 ≤ R₃) (hUR : U ≤ R₃)
    (hC : 0 ≤ C) :
    C * U ^ 4 * Z ^ 2 * (R₁ ^ 2 / (U * Z)) *
        (R₂ ^ 2 / (U * Z)) * (R₃ / U) ≤ C * (R₁ * R₂ * R₃) ^ 2 := by
  have heq : C * U ^ 4 * Z ^ 2 * (R₁ ^ 2 / (U * Z)) *
      (R₂ ^ 2 / (U * Z)) * (R₃ / U) = C * R₁ ^ 2 * R₂ ^ 2 * R₃ * U := by
    field_simp
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_left hUR
    (show 0 ≤ C * R₁ ^ 2 * R₂ ^ 2 * R₃ by positivity)
  nlinarith

theorem thin_normal_group_numeric {U Y R₁ R₂ R₃ C : ℝ}
    (hU : 0 < U) (hY : 0 < Y) (hR : 0 ≤ R₃) (hUR : U ≤ R₃)
    (hC : 0 ≤ C) :
    C * U ^ 2 * Y ^ 2 * (R₁ ^ 2 / Y) *
        (R₂ ^ 2 / Y) * (R₃ / U) ≤ C * (R₁ * R₂ * R₃) ^ 2 := by
  have heq : C * U ^ 2 * Y ^ 2 * (R₁ ^ 2 / Y) *
      (R₂ ^ 2 / Y) * (R₃ / U) = C * R₁ ^ 2 * R₂ ^ 2 * R₃ * U := by
    field_simp
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_left hUR
    (show 0 ≤ C * R₁ ^ 2 * R₂ ^ 2 * R₃ by positivity)
  nlinarith

theorem dyadic_log_product_le {R₁ R₂ R₃ : ℝ}
    (h₂ : 1 ≤ R₂) (h₃ : 1 ≤ R₃) (h₂₁ : R₂ ≤ R₁) (h₃₁ : R₃ ≤ R₁) :
    (Real.log (2 * R₃) / Real.log 2) *
      (Real.log (2 * (R₂ * R₃)) / Real.log 2) ≤
        2 * (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
  have h₁ : 1 ≤ R₁ := h₂.trans h₂₁
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ Real.log (2 * R₁) / Real.log 2 := by
    apply div_nonneg _ hlog2.le
    exact Real.log_nonneg (by linarith)
  have hleft : Real.log (2 * R₃) / Real.log 2 ≤
      Real.log (2 * R₁) / Real.log 2 := by
    apply div_le_div_of_nonneg_right _ hlog2.le
    exact Real.log_le_log (by linarith) (by linarith)
  have hmul : R₂ * R₃ ≤ R₁ * R₁ :=
    mul_le_mul h₂₁ h₃₁ (by linarith) (by linarith)
  have hright : Real.log (2 * (R₂ * R₃)) / Real.log 2 ≤
      2 * (Real.log (2 * R₁) / Real.log 2) := by
    have hp : 0 < 2 * (R₂ * R₃) := by positivity
    have hr : Real.log (2 * (R₂ * R₃)) ≤ 2 * Real.log (2 * R₁) := by
      calc
        Real.log (2 * (R₂ * R₃)) ≤ Real.log ((2 * R₁) ^ 2) :=
          Real.log_le_log hp (by nlinarith [sq_nonneg R₁])
        _ = _ := by rw [Real.log_pow]; norm_num
    have := div_le_div_of_nonneg_right hr hlog2.le
    simpa [mul_div_assoc] using this
  have hright0 : 0 ≤ Real.log (2 * (R₂ * R₃)) / Real.log 2 := by
    apply div_nonneg _ hlog2.le
    apply Real.log_nonneg
    nlinarith
  have hprod := mul_le_mul hleft hright hright0 hL
  nlinarith

theorem sum_le_of_dyadic_shell_estimates {α : Type*} [DecidableEq α]
    (S : Finset α) (u v weight : α → ℝ) {R T A : ℝ}
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hA : 0 ≤ A)
    (hweight : ∀ x ∈ S, 0 ≤ weight x)
    (hvalue : ∀ x ∈ S, 1 ≤ u x ∧ u x ≤ R ∧ 1 ≤ v x ∧ v x ≤ T)
    (hshell : ∀ i j : ℕ,
      ∑ x ∈ S with ((2 : ℝ) ^ i ≤ u x ∧ u x < 2 ^ (i + 1) ∧
        (2 : ℝ) ^ j ≤ v x ∧ v x < 2 ^ (j + 1)), weight x ≤ A) :
    ∑ x ∈ S, weight x ≤
      A * (Real.log (2 * R) / Real.log 2) * (Real.log (2 * T) / Real.log 2) := by
  classical
  have hex : ∀ x : α, ∃ p : ℕ × ℕ, x ∈ S →
      (2 : ℝ) ^ p.1 ≤ u x ∧ u x < 2 ^ (p.1 + 1) ∧
      (2 : ℝ) ^ p.2 ≤ v x ∧ v x < 2 ^ (p.2 + 1) := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨i, hi, hi'⟩ := exists_nat_pow_near (hvalue x hx).1 (by norm_num : (1 : ℝ) < 2)
      obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near (hvalue x hx).2.2.1 (by norm_num : (1 : ℝ) < 2)
      exact ⟨(i,j), fun _ => ⟨hi, hi', hj, hj'⟩⟩
    · exact ⟨(0,0), fun h => (hx h).elim⟩
  choose index hindex using hex
  apply sum_le_of_dyadic_fibers S index weight hR hT hA
  · intro x hx
    exact ⟨(hindex x hx).1.trans (hvalue x hx).2.1,
      (hindex x hx).2.2.1.trans (hvalue x hx).2.2.2⟩
  · intro p hp
    have hsub : (S.filter fun x => index x = p) ⊆
        (S.filter fun x => (2 : ℝ) ^ p.1 ≤ u x ∧ u x < 2 ^ (p.1 + 1) ∧
          (2 : ℝ) ^ p.2 ≤ v x ∧ v x < 2 ^ (p.2 + 1)) := by
      intro x hx
      obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨hxS, ?_⟩
      simpa [hxp] using hindex x hxS
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x hx _ => hweight x (Finset.mem_filter.mp hx).1)).trans (hshell p.1 p.2)

theorem sum_le_of_single_dyadic_shell_estimates {α : Type*} [DecidableEq α]
    (S : Finset α) (u weight : α → ℝ) {R A : ℝ}
    (hR : 1 ≤ R) (hA : 0 ≤ A)
    (hweight : ∀ x ∈ S, 0 ≤ weight x)
    (hvalue : ∀ x ∈ S, 1 ≤ u x ∧ u x ≤ R)
    (hshell : ∀ i : ℕ,
      ∑ x ∈ S with ((2 : ℝ) ^ i ≤ u x ∧ u x < 2 ^ (i + 1)), weight x ≤ A) :
    ∑ x ∈ S, weight x ≤ A * (Real.log (2 * R) / Real.log 2) := by
  have h := sum_le_of_dyadic_shell_estimates S u (fun _ => 1) weight
    hR (by norm_num : (1 : ℝ) ≤ 1) hA hweight
    (fun x hx => ⟨(hvalue x hx).1, (hvalue x hx).2, le_rfl, le_rfl⟩)
  have hs : ∀ i j : ℕ,
      ∑ x ∈ S with ((2 : ℝ) ^ i ≤ u x ∧ u x < 2 ^ (i + 1) ∧
        (2 : ℝ) ^ j ≤ 1 ∧ (1 : ℝ) < 2 ^ (j + 1)), weight x ≤ A := by
    intro i j
    apply le_trans _ (hshell i)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      obtain ⟨hxS, hx⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hxS, hx.1, hx.2.1⟩
    · intro x hx _
      exact hweight x (Finset.mem_filter.mp hx).1
  simpa [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))] using h hs

end Problem355.Anisotropic

end

end OAI
