import Mathlib

namespace OAI

open scoped BigOperators

namespace PiExponent.FiniteSpacing

theorem lower_bound_of_spacing {N : ℕ} (x : Fin N → ℝ) {d : ℝ}
    (hmin : ∀ i, d ≤ x i)
    (hsep : ∀ i j, i < j → d ≤ x j - x i) :
    ∀ i, ((i.val : ℝ) + 1) * d ≤ x i := by
  have aux : ∀ k (hk : k < N), ((k : ℝ) + 1) * d ≤ x ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      simpa using hmin ⟨0, hk⟩
    | succ k ih =>
      intro hk
      have hk' : k < N := Nat.lt_trans (Nat.lt_succ_self k) hk
      have hp := ih hk'
      have hs := hsep ⟨k, hk'⟩ ⟨k + 1, hk⟩ (by simp)
      push_cast
      linarith
  intro i
  exact aux i.val i.isLt

theorem sum_inv_succ_sq_le_two_sub (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 2) ≤
      2 - 2 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    have hterm : 1 / ((N : ℝ) + 1) ^ 2 ≤
        2 / ((N : ℝ) + 1) - 2 / ((N : ℝ) + 2) := by
      field_simp
      nlinarith
    push_cast
    convert add_le_add ih hterm using 1
    ring

theorem sum_inv_succ_sq_le_two (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 2) ≤ 2 := by
  have h := sum_inv_succ_sq_le_two_sub N
  have hnonneg : 0 ≤ 2 / ((N : ℝ) + 1) := by positivity
  linarith

theorem sum_inv_sq_le_two_div_sq_of_spacing {N : ℕ}
    (x : Fin N → ℝ) {d : ℝ} (hd : 0 < d)
    (hmin : ∀ i, d ≤ x i)
    (hsep : ∀ i j, i < j → d ≤ x j - x i) :
    (∑ i, 1 / (x i) ^ 2) ≤ 2 / d ^ 2 := by
  have hlower := lower_bound_of_spacing x hmin hsep
  calc
    (∑ i, 1 / (x i) ^ 2) ≤
        ∑ i : Fin N, 1 / ((((i.val : ℝ) + 1) * d) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hpos : 0 < ((i.val : ℝ) + 1) * d := by positivity
      exact one_div_le_one_div_of_le (sq_pos_of_pos hpos)
        (pow_le_pow_left₀ hpos.le (hlower i) 2)
    _ = (1 / d ^ 2) * ∑ i : Fin N, 1 / ((i.val : ℝ) + 1) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, one_div_mul_one_div]
      ring
    _ ≤ (1 / d ^ 2) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2)]
      exact sum_inv_succ_sq_le_two N
    _ = 2 / d ^ 2 := by ring

theorem sum_inv_sq_le_two_div_sq (s : Finset ℝ) {d : ℝ} (hd : 0 < d)
    (hmin : ∀ x ∈ s, d ≤ x)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ |x - y|) :
    (∑ x ∈ s, 1 / x ^ 2) ≤ 2 / d ^ 2 := by
  classical
  let e := s.orderEmbOfFin rfl
  have hmem : ∀ i, e i ∈ s := fun i => s.orderEmbOfFin_mem rfl i
  have hstep : ∀ i j, i < j → d ≤ e j - e i := by
    intro i j hij
    have hij' : e i < e j := e.strictMono hij
    have h := hsep (e j) (hmem j) (e i) (hmem i) (ne_of_gt hij')
    rwa [abs_of_pos (sub_pos.mpr hij')] at h
  have hbound := sum_inv_sq_le_two_div_sq_of_spacing e hd
    (fun i => hmin (e i) (hmem i)) hstep
  have hsum : (∑ i : Fin s.card, 1 / (e i) ^ 2) = ∑ x ∈ s, 1 / x ^ 2 := by
    have himage : Finset.univ.image e = s := s.image_orderEmbOfFin_univ rfl
    calc
      _ = ∑ y ∈ Finset.univ.image e, 1 / y ^ 2 :=
        (Finset.sum_image e.injective.injOn).symm
      _ = _ := congrArg (fun t : Finset ℝ => ∑ y ∈ t, 1 / y ^ 2) himage
  rwa [hsum] at hbound

theorem sum_inv_sq_le_two_div_sq_indexed {ι : Type*}
    (rows : Finset ι) (x : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hmin : ∀ i ∈ rows, d ≤ x i)
    (hsep : ∀ i ∈ rows, ∀ j ∈ rows, i ≠ j → d ≤ |x i - x j|) :
    (∑ i ∈ rows, 1 / (x i) ^ 2) ≤ 2 / d ^ 2 := by
  classical
  have hinj : Set.InjOn x (rows : Set ι) := by
    intro i hi j hj h
    by_contra hij
    have hs := hsep i hi j hj hij
    rw [h, sub_self, abs_zero] at hs
    exact (not_le_of_gt hd) hs
  have h := sum_inv_sq_le_two_div_sq (rows.image x) hd
    (by intro a ha; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha; exact hmin i hi)
    (by
      intro a ha b hb hab
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      exact hsep i hi j hj (fun hij => hab (congrArg x hij)))
  rwa [Finset.sum_image hinj] at h

end PiExponent.FiniteSpacing

end OAI
