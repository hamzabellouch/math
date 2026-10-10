import OAI.NumberTheory.JointDickman.Amplification.CutBounds
import Mathlib.Algebra.Order.BigOperators.Expect

namespace OAI

/-!
# A small-column sampling skeleton

This is the deterministic part of `sampling-skeleton` in the manuscript.
Sampling with replacement allows repeated columns; their multiplicities are
retained in the row response.  The number of distinct columns is at most the
sample size.  No probabilistic or cut-approximation hypothesis is assumed.
-/

open scoped BigOperators
open Finset

namespace JointDickman

attribute [local instance] Classical.propDecidable

/-- The best-response sign, with the manuscript's convention at zero. -/
noncomputable def responseSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

@[simp] theorem abs_responseSign (x : ℝ) : |responseSign x| = 1 := by
  unfold responseSign
  split_ifs <;> norm_num

theorem mul_responseSign (x : ℝ) : x * responseSign x = |x| := by
  unfold responseSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem responseSign_pos_mul {a : ℝ} (ha : 0 < a) (x : ℝ) :
    responseSign (a * x) = responseSign x := by
  simp [responseSign, mul_nonneg_iff_of_pos_left ha]

/-- A mistaken best response costs at most twice its prediction error. -/
theorem responseSign_loss (x y : ℝ) :
    |x| - x * responseSign y ≤ 2 * |x - y| := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · simp [responseSign, hy, abs_of_nonneg hx, abs_nonneg]
  · rw [responseSign, ite_eq_right hy, abs_of_nonneg hx,
      abs_of_nonneg (sub_nonneg.mpr (le_trans (le_of_not_ge hy) hx))]
    linarith
  · rw [responseSign, ite_eq_left hy, abs_of_neg (lt_of_not_ge hx),
      abs_of_nonpos (sub_nonpos.mpr (le_trans (le_of_not_ge hx) hy))]
    linarith
  · simp [responseSign, hy, abs_of_neg (lt_of_not_ge hx), abs_nonneg]

theorem sum_abs_le_sqrt_card_mul_sum_sq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, |f i|) ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, f i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset ι)
    (fun _ => (1 : ℝ)) (fun i => |f i|)
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one,
    sq_abs] at h
  exact (Real.le_sqrt (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)).2 h

/-- An L² approximation to the row sums gives an L¹ best-response loss. -/
theorem sum_responseSign_loss {ι : Type*} [Fintype ι] (r q : ι → ℝ) :
    (∑ i, |r i|) ≤ (∑ i, r i * responseSign (q i)) +
      2 * Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, (r i - q i) ^ 2) := by
  have h := sum_le_sum (s := (univ : Finset ι)) (fun i _ => responseSign_loss (r i) (q i))
  rw [sum_sub_distrib, ← mul_sum] at h
  have hs := sum_abs_le_sqrt_card_mul_sum_sq (fun i => r i - q i)
  linarith

private theorem expect_coordinate_product {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]
    (f : J → A → ℝ) :
    (𝔼 σ : J → A, ∏ j, f j (σ j)) = ∏ j, 𝔼 a : A, f j a := by
  simp only [Fintype.expect_eq_sum_div_card, prod_div_distrib, prod_const, card_univ,
    Fintype.card_fun, Nat.cast_pow]
  congr 1
  simpa using (prod_univ_sum (fun _ : J => (univ : Finset A)) f).symm

private theorem expect_coordinate {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A] [Nonempty A]
    (j : J) (f : A → ℝ) : (𝔼 σ : J → A, f (σ j)) = 𝔼 a : A, f a := by
  classical
  have h := expect_coordinate_product (fun k a => if k = j then f a else 1)
  have hl (σ : J → A) : (∏ k, if k = j then f (σ k) else 1) = f (σ j) := by simp
  have hr : (∏ k : J, 𝔼 a : A, if k = j then f a else 1) = 𝔼 a : A, f a := by
    rw [prod_eq_single j]
    · simp
    · intro k _ hkj
      simp [hkj]
    · simp
  simpa only [hl, hr] using h

private theorem expect_distinct_coordinates {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]
    [Nonempty A] {j k : J} (hjk : j ≠ k) (f g : A → ℝ) :
    (𝔼 σ : J → A, f (σ j) * g (σ k)) = (𝔼 a : A, f a) * 𝔼 a : A, g a := by
  classical
  let w : J → A → ℝ := fun l a => if l = j then f a else if l = k then g a else 1
  have hw (σ : J → A) : (∏ l, w l (σ l)) = f (σ j) * g (σ k) := by
    rw [Finset.prod_eq_mul_of_mem j k (mem_univ _) (mem_univ _) hjk]
    · simp [w, hjk.symm]
    · intro l _ ⟨hlj, hlk⟩
      simp [w, hlj, hlk]
  have he : (∏ l, 𝔼 a : A, w l a) = (𝔼 a : A, f a) * 𝔼 a : A, g a := by
    rw [Finset.prod_eq_mul_of_mem j k (mem_univ _) (mem_univ _) hjk]
    · simp [w, hjk.symm]
    · intro l _ ⟨hlj, hlk⟩
      simp [w, hlj, hlk]
  simpa only [hw, he] using expect_coordinate_product w

/-- Independent, centered coordinate samples have no off-diagonal terms. -/
theorem expect_sample_sum_sq {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A] [Nonempty A]
    (f : A → ℝ) (hf : (𝔼 a : A, f a) = 0) :
    (𝔼 σ : J → A, (∑ j, f (σ j)) ^ 2) =
      (Fintype.card J : ℝ) * (𝔼 a : A, f a ^ 2) := by
  classical
  simp_rw [pow_two, sum_mul, mul_sum]
  rw [expect_sum_comm]
  simp_rw [expect_sum_comm]
  have hpair (j k : J) : (𝔼 σ : J → A, f (σ j) * f (σ k)) =
      if j = k then (𝔼 a : A, f a ^ 2) else 0 := by
    by_cases h : j = k
    · subst k
      simpa only [pow_two, ite_true] using
        (expect_coordinate (J := J) j (fun a => f a * f a))
    · rw [expect_distinct_coordinates h, hf, zero_mul, ite_eq_right h]
  simp_rw [hpair]
  simp [pow_two]

/-- The usual finite-population variance identity. -/
theorem expect_centered_sq {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    (𝔼 a : A, (f a - (𝔼 b : A, f b)) ^ 2) =
      (𝔼 a : A, f a ^ 2) - (𝔼 a : A, f a) ^ 2 := by
  simp_rw [sub_sq, expect_add_distrib, expect_sub_distrib]
  rw [Fintype.expect_const, ← Finset.expect_mul, ← mul_expect]
  ring

/-- Mean-square error for independent uniform samples, with replacement. -/
theorem expect_sample_mean_sq_le {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) (m : ℕ) (hm : 0 < m) :
    (𝔼 σ : Fin m → A,
      ((∑ j, f (σ j)) / m - (𝔼 a : A, f a)) ^ 2) ≤
        (𝔼 a : A, f a ^ 2) / m := by
  let μ := 𝔼 a : A, f a
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : (𝔼 a : A, (f a - μ)) = 0 := by
    rw [expect_sub_distrib, Fintype.expect_const]
    exact sub_self _
  have he (σ : Fin m → A) :
      (∑ j, f (σ j)) / m - μ = (∑ j, (f (σ j) - μ)) / m := by
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  change (𝔼 σ : Fin m → A, ((∑ j, f (σ j)) / m - μ) ^ 2) ≤ _
  simp_rw [he, div_pow]
  rw [← expect_div, expect_sample_sum_sq (J := Fin m) (fun a => f a - μ) hc]
  simp only [Fintype.card_fin]
  rw [show (𝔼 a : A, (f a - μ) ^ 2) = (𝔼 a : A, f a ^ 2) - μ ^ 2 from
    expect_centered_sq f]
  calc
    _ = ((𝔼 a : A, f a ^ 2) - μ ^ 2) / m := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg μ)) hmpos.le

/-- The column estimator approximates every row simultaneously in squared error. -/
theorem exists_column_sample_sq_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (K : ι → ι → ℝ) (δ : ι → ℝ) (hδ : ∀ j, |δ j| = 1)
    (m : ℕ) (hm : 0 < m) :
    ∃ σ : Fin m → ι,
      (∑ i, ((∑ j, K i j * δ j) -
        (Fintype.card ι : ℝ) / m * ∑ a, K i (σ a) * δ (σ a)) ^ 2) ≤
          (Fintype.card ι : ℝ) / m * ∑ i, ∑ j, K i j ^ 2 := by
  classical
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hrow (i : ι) :
      (𝔼 σ : Fin m → ι, ((∑ j, K i j * δ j) -
        (Fintype.card ι : ℝ) / m * ∑ a, K i (σ a) * δ (σ a)) ^ 2) ≤
          (Fintype.card ι : ℝ) / m * ∑ j, K i j ^ 2 := by
    have hh := expect_sample_mean_sq_le (fun j => K i j * δ j) m hm
    have hd (j : ι) : (K i j * δ j) ^ 2 = K i j ^ 2 := by
      have hs : (δ j) ^ 2 = 1 := by nlinarith [sq_abs (δ j), hδ j]
      rw [mul_pow, hs, mul_one]
    have he (σ : Fin m → ι) :
        ((∑ j, K i j * δ j) -
          (Fintype.card ι : ℝ) / m * ∑ a, K i (σ a) * δ (σ a)) ^ 2 =
        (Fintype.card ι : ℝ) ^ 2 *
          ((∑ a, K i (σ a) * δ (σ a)) / m -
            (𝔼 j : ι, K i j * δ j)) ^ 2 := by
      rw [Fintype.expect_eq_sum_div_card]
      field_simp
      ring
    simp_rw [he]
    rw [← mul_expect]
    refine (mul_le_mul_of_nonneg_left hh (sq_nonneg _)).trans_eq ?_
    simp_rw [hd]
    rw [Fintype.expect_eq_sum_div_card]
    field_simp
  have hmean :
      (𝔼 σ : Fin m → ι, ∑ i, ((∑ j, K i j * δ j) -
        (Fintype.card ι : ℝ) / m * ∑ a, K i (σ a) * δ (σ a)) ^ 2) ≤
          (Fintype.card ι : ℝ) / m * ∑ i, ∑ j, K i j ^ 2 := by
    rw [expect_sum_comm, mul_sum]
    exact sum_le_sum (fun i _ => hrow i)
  obtain ⟨σ, _, hσ⟩ := exists_le_of_expect_le (s := (univ : Finset (Fin m → ι)))
    univ_nonempty hmean
  exact ⟨σ, hσ⟩

/-- Removing a set of indices costs at most its row and column mass. -/
theorem delete_endpoints_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ) (hsym : ∀ i j, K i j = K j i)
    (d : ℝ) (hrow : ∀ i, (∑ j, |K i j|) ≤ d)
    (T : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    realBilinear K f g ≤
      (∑ i ∈ univ \ T, ∑ j ∈ univ \ T, K i j * f i * g j) +
        2 * T.card * d := by
  let R := univ \ T
  have hpart (a : ι → ℝ) : (∑ i, a i) = (∑ i ∈ R, a i) + ∑ i ∈ T, a i := by
    exact (sum_sdiff (f := a) (subset_univ T)).symm
  have hterm (i j : ι) : |K i j * f i * g j| ≤ |K i j| := by
    rw [abs_mul, abs_mul]
    calc
      |K i j| * |f i| * |g j| ≤ |K i j| * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)) (hg j)
          (abs_nonneg _) (by positivity)
      _ = |K i j| := by ring
  have hremoved : (∑ i ∈ T, ∑ j, K i j * f i * g j) ≤ T.card * d := by
    calc
      _ ≤ ∑ i ∈ T, ∑ j, |K i j| := by
        exact sum_le_sum fun i _ => sum_le_sum fun j _ => (le_abs_self _).trans (hterm i j)
      _ ≤ ∑ _i ∈ T, d := sum_le_sum fun i _ => hrow i
      _ = _ := by simp
  have hcross : (∑ i ∈ R, ∑ j ∈ T, K i j * f i * g j) ≤ T.card * d := by
    rw [sum_comm]
    calc
      _ ≤ ∑ j ∈ T, ∑ i ∈ R, |K j i| := by
        apply sum_le_sum
        intro j _
        apply sum_le_sum
        intro i _
        rw [← hsym i j]
        exact (le_abs_self _).trans (hterm i j)
      _ ≤ ∑ j ∈ T, ∑ i, |K j i| := by
        exact sum_le_sum fun j _ => sum_le_sum_of_subset_of_nonneg (subset_univ R)
          (fun _ _ _ => abs_nonneg _)
      _ ≤ ∑ _j ∈ T, d := sum_le_sum fun j _ => hrow j
      _ = _ := by simp
  have he : realBilinear K f g =
      (∑ i ∈ R, ∑ j ∈ R, K i j * f i * g j) +
      (∑ i ∈ R, ∑ j ∈ T, K i j * f i * g j) +
      (∑ i ∈ T, ∑ j, K i j * f i * g j) := by
    unfold realBilinear
    rw [hpart]
    conv_lhs => arg 1; arg 2; ext i; rw [hpart]
    rw [sum_add_distrib]
  change _ ≤ (∑ i ∈ R, ∑ j ∈ R, K i j * f i * g j) + _
  linarith

/-- The response obtained from an ordered sample of columns. -/
noncomputable def sampledResponse {ι : Type*} {m : ℕ}
    (K : ι → ι → ℝ) (δ : ι → ℝ) (σ : Fin m → ι) (i : ι) : ℝ :=
  responseSign (∑ a, K i (σ a) * δ (σ a))

/-- The residual column optimum after deleting the sampled endpoints. -/
noncomputable def residualColumnBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ) (T : Finset ι) (g : ι → ℝ) : ℝ :=
  ∑ j ∈ univ \ T, |∑ i ∈ univ \ T, K i j * g i|

/-- A fixed column-sign vector has a small-column best response with explicit loss. -/
theorem exists_sampled_response_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (K : ι → ι → ℝ) (hsym : ∀ i j, K i j = K j i)
    (d : ℝ) (hrow : ∀ i, (∑ j, |K i j|) ≤ d)
    (δ : ι → ℝ) (hδ : ∀ j, |δ j| = 1) (m : ℕ) (hm : 0 < m) :
    ∃ σ : Fin m → ι,
      (∑ i, |∑ j, K i j * δ j|) ≤
        residualColumnBound K (univ.image σ) (sampledResponse K δ σ) +
        2 * Real.sqrt ((Fintype.card ι : ℝ) *
          ((Fintype.card ι : ℝ) / m * ∑ i, ∑ j, K i j ^ 2)) + 2 * m * d := by
  obtain ⟨σ, hσ⟩ := exists_column_sample_sq_le K δ hδ m hm
  refine ⟨σ, ?_⟩
  let g := sampledResponse K δ σ
  let T := univ.image σ
  have hg (i : ι) : |g i| ≤ 1 := by simp [g, sampledResponse]
  have hd : 0 ≤ d := (sum_nonneg fun _ _ => abs_nonneg _).trans (hrow (Classical.arbitrary ι))
  have hcard : (T.card : ℝ) ≤ m := by
    exact_mod_cast (show (univ.image σ).card ≤ m by simpa using card_image_le (f := σ) (s := univ))
  have hpos : 0 < (Fintype.card ι : ℝ) / m := by positivity
  have hresp : (∑ i, |∑ j, K i j * δ j|) ≤ realBilinear K g δ +
      2 * Real.sqrt ((Fintype.card ι : ℝ) *
        ((Fintype.card ι : ℝ) / m * ∑ i, ∑ j, K i j ^ 2)) := by
    have hl := sum_responseSign_loss (fun i => ∑ j, K i j * δ j)
      (fun i => (Fintype.card ι : ℝ) / m * ∑ a, K i (σ a) * δ (σ a))
    have he : (∑ i, (∑ j, K i j * δ j) *
        responseSign ((Fintype.card ι : ℝ) / m * ∑ a, K i (σ a) * δ (σ a))) =
        realBilinear K g δ := by
      simp only [responseSign_pos_mul hpos, realBilinear, g, sampledResponse, sum_mul]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    rw [he] at hl
    have hroot := Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left hσ (Nat.cast_nonneg (Fintype.card ι)))
    linarith
  have hdelete := delete_endpoints_bound K hsym d hrow T g δ hg (fun j => (hδ j).le)
  have hremaining : (∑ i ∈ univ \ T, ∑ j ∈ univ \ T, K i j * g i * δ j) ≤
      residualColumnBound K T g := by
    rw [sum_comm]
    apply sum_le_sum
    intro j _
    rw [← sum_mul]
    calc
      (∑ i ∈ univ \ T, K i j * g i) * δ j ≤
          |(∑ i ∈ univ \ T, K i j * g i) * δ j| := le_abs_self _
      _ = |∑ i ∈ univ \ T, K i j * g i| := by rw [abs_mul, hδ, mul_one]
  dsimp only [T, g] at hdelete hremaining ⊢
  nlinarith [mul_le_mul_of_nonneg_right hcard hd]

/-- A single sampled response controls every sign cut of a symmetric matrix.
The witness depends only on the matrix and uses at most `m` distinct columns. -/
theorem exists_small_column_skeleton {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (K : ι → ι → ℝ) (hsym : ∀ i j, K i j = K j i)
    (d : ℝ) (hrow : ∀ i, (∑ j, |K i j|) ≤ d) (m : ℕ) (hm : 0 < m) :
    ∃ δ : ι → Bool, ∃ σ : Fin m → ι,
      (univ.image σ).card ≤ m ∧ ∀ s t : ι → Bool,
        |realBilinear K (fun i => cutSign (s i)) (fun j => cutSign (t j))| ≤
          residualColumnBound K (univ.image σ)
            (sampledResponse K (fun j => cutSign (δ j)) σ) +
          2 * Real.sqrt ((Fintype.card ι : ℝ) *
            ((Fintype.card ι : ℝ) / m * ∑ i, ∑ j, K i j ^ 2)) + 2 * m * d := by
  classical
  let F : (ι → Bool) → ℝ := fun t => ∑ i, |∑ j, K i j * cutSign (t j)|
  obtain ⟨δ, _, hmax⟩ := (univ : Finset (ι → Bool)).exists_max_image F univ_nonempty
  obtain ⟨σ, hσ⟩ := exists_sampled_response_bound K hsym d hrow
    (fun j => cutSign (δ j)) (fun j => abs_cutSign (δ j)) m hm
  refine ⟨δ, σ, by simpa using card_image_le (f := σ) (s := univ), ?_⟩
  intro s t
  have he : realBilinear K (fun i => cutSign (s i)) (fun j => cutSign (t j)) =
      ∑ i, (∑ j, K i j * cutSign (t j)) * cutSign (s i) := by
    simp only [realBilinear, sum_mul]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  calc
    _ ≤ ∑ i, |(∑ j, K i j * cutSign (t j)) * cutSign (s i)| := by
      rw [he]
      exact abs_sum_le_sum_abs _ _
    _ = F t := by simp [F, abs_mul, abs_cutSign]
    _ ≤ F δ := hmax t (mem_univ _)
    _ ≤ _ := hσ

end JointDickman

end OAI
