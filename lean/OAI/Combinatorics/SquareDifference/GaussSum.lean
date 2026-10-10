import Mathlib

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

def IsSquareDifferenceFree (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, 1 ≤ m → a - b ≠ (m : ℤ) ^ 2

def PowerSaving : Prop :=
  ∃ c C : ℝ, 0 < c ∧
    ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℤ,
      A ⊆ Finset.Icc 1 (N : ℤ) → IsSquareDifferenceFree A →
      (A.card : ℝ) ≤ C * (N : ℝ) ^ (1 - c)

lemma gaussSum_norm_sq {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) : ‖gaussSum χ ψ‖ ^ 2 = Fintype.card F := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hr := congrArg Complex.re h
  simpa [Complex.mul_conj, Complex.sq_norm] using hr

lemma square_sum_eq_gaussSum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∑ a : F, ψ (a ^ 2) =
      gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ := by
  classical
  calc
    ∑ a : F, ψ (a ^ 2) =
        ∑ b : F, ∑ a ∈ (univ.filter fun a : F => a ^ 2 = b), ψ (a ^ 2) :=
      (sum_fiberwise univ (fun a : F => a ^ 2) (fun a => ψ (a ^ 2))).symm
    _ = ∑ b : F, ((quadraticChar F b : ℂ) + 1) * ψ b := by
      apply sum_congr rfl
      intro b _
      have hc : ((univ.filter fun a : F => a ^ 2 = b).card : ℂ) =
          (quadraticChar F b : ℂ) + 1 := by
        have hc' := quadraticChar_card_sqrts hF b
        simp only [Set.toFinset_ofPred] at hc'
        exact_mod_cast hc'
      simp_rw [sum_congr rfl (fun a ha => congrArg ψ (mem_filter.mp ha).2)]
      simp only [sum_const, nsmul_eq_mul, hc]
    _ = gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ := by
      simp [add_mul, sum_add_distrib, AddChar.sum_eq_zero_of_ne_one hψ, gaussSum]

lemma square_sum_norm_sq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖∑ a : F, ψ (a ^ 2)‖ ^ 2 = Fintype.card F := by
  have hp : ψ ≠ 1 := by simpa using hψ (show (1 : F) ≠ 0 from one_ne_zero)
  rw [square_sum_eq_gaussSum hF hp]
  apply gaussSum_norm_sq _ hψ
  exact (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ) Int.cast_injective).mpr (quadraticChar_ne_one hF)

noncomputable def squareIndicator {F : Type*} [Field F] (x : F) : ℝ :=
  by
  classical
  exact if x ≠ 0 ∧ IsSquare x then 1 else 0

lemma squareIndicator_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (x : F) : squareIndicator x =
      ((quadraticChar F x : ℝ) + 1 - if x = 0 then 1 else 0) / 2 := by
  classical
  by_cases hx : x = 0
  · simp [hx, squareIndicator]
  by_cases hs : IsSquare x
  · simp [squareIndicator, hx, hs, (quadraticChar_one_iff_isSquare hx).mpr hs]
  · simp [squareIndicator, hx, hs, quadraticChar_neg_one_iff_not_isSquare.mpr hs]

lemma squareIndicator_nonneg {F : Type*} [Field F] (x : F) :
    0 ≤ squareIndicator x := by
  classical
  unfold squareIndicator
  split_ifs <;> norm_num

lemma squareIndicator_le_one {F : Type*} [Field F] (x : F) :
    squareIndicator x ≤ 1 := by
  classical
  unfold squareIndicator
  split_ifs <;> norm_num

lemma squareIndicator_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) :
    ∑ x : F, squareIndicator x = (Fintype.card F - 1 : ℝ) / 2 := by
  classical
  simp_rw [squareIndicator_eq, sub_div, add_div, sum_sub_distrib, sum_add_distrib,
    ← sum_div]
  have hz : ∑ x : F, (quadraticChar F x : ℝ) = 0 := by
    exact_mod_cast quadraticChar_sum_zero hF
  rw [hz]
  simp only [zero_div, zero_add, sum_const, card_univ, nsmul_eq_mul, mul_one,
    sum_ite_eq', mem_univ, ite_true]

lemma squareIndicator_char_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∑ x : F, (squareIndicator x : ℂ) * ψ x =
      (∑ x : F, ψ (x ^ 2) - 1) / 2 := by
  classical
  rw [square_sum_eq_gaussSum hF hψ]
  simp_rw [squareIndicator_eq, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  simp_rw [sub_div, add_div, sub_mul, add_mul, sum_sub_distrib, sum_add_distrib]
  have hcast (x : F) : ((if x = 0 then 1 else 0 : ℝ) : ℂ) =
      if x = 0 then 1 else 0 := by split_ifs <;> simp
  simp_rw [hcast, div_mul_eq_mul_div, ← sum_div]
  simp [AddChar.sum_eq_zero_of_ne_one hψ, gaussSum]

lemma squareIndicator_char_sum_norm {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖∑ x : F, (squareIndicator x : ℂ) * ψ x‖ ≤
      (Real.sqrt (Fintype.card F) + 1) / 2 := by
  have hp : ψ ≠ 1 := by simpa using hψ (show (1 : F) ≠ 0 from one_ne_zero)
  have hnorm : ‖∑ a : F, ψ (a ^ 2)‖ = Real.sqrt (Fintype.card F) := by
    rw [← square_sum_norm_sq hF hψ, Real.sqrt_sq (norm_nonneg _)]
  rw [squareIndicator_char_sum hF hp, norm_div]
  norm_num only [Complex.norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  calc
    ‖(∑ a : F, ψ (a ^ 2)) - 1‖ ≤ ‖∑ a : F, ψ (a ^ 2)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = Real.sqrt (Fintype.card F) + 1 := by rw [hnorm, norm_one]

lemma dft_inner {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    ∑ k : ZMod N, star (ZMod.dft f k) * ZMod.dft g k =
      (N : ℂ) * ∑ x : ZMod N, star (f x) * g x := by
  classical
  have hs (x : ZMod N) : star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) :=
    (AddChar.map_neg_eq_conj _ x).symm
  simp_rw [ZMod.dft_apply, smul_eq_mul, star_sum, star_mul, hs, neg_neg,
    sum_mul, mul_sum]
  have hprod (k x y : ZMod N) :
      star (f x) * ZMod.stdAddChar (x * k) *
          (ZMod.stdAddChar (-(y * k)) * g y) =
      ZMod.stdAddChar (k * (x - y)) * (star (f x) * g y) := by
    rw [mul_comm (star (f x)), mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [hprod]
  rw [sum_comm]
  simp_rw [sum_comm (f := fun k y : ZMod N =>
    ZMod.stdAddChar (k * ( _ - y)) * (star (f _) * g y))]
  simp_rw [← sum_mul, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  simp only [Nat.cast_ite, ZMod.card, Nat.cast_zero, ite_mul, zero_mul,
    sub_eq_zero, sum_ite_eq, mem_univ, ite_true]

lemma dft_parseval {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖ZMod.dft f k‖ ^ 2 =
      (N : ℝ) * ∑ x : ZMod N, ‖f x‖ ^ 2 := by
  have h := dft_inner f f
  simp_rw [← starRingEnd_apply, Complex.conj_mul'] at h
  exact_mod_cast h

lemma dft_convolution {N : ℕ} [NeZero N] (a b : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun x => ∑ y : ZMod N, a (x - y) * b y) k =
      ZMod.dft a k * ZMod.dft b k := by
  classical
  simp only [ZMod.dft_apply, smul_eq_mul, mul_sum]
  rw [sum_comm]
  have hshift (y : ZMod N) :
      ∑ x : ZMod N, ZMod.stdAddChar (-(x * k)) * (a (x - y) * b y) =
        ∑ t : ZMod N, ZMod.stdAddChar (-((t + y) * k)) * (a t * b y) := by
    apply Fintype.sum_equiv (Equiv.subRight y)
    intro x
    simp
  simp_rw [hshift, add_mul, neg_add, AddChar.map_add_eq_mul]
  apply sum_congr rfl
  intro y _
  rw [sum_mul]
  apply sum_congr rfl
  intro x _
  ring

lemma convolution_l2_sq_le {N : ℕ} [NeZero N] (a b : ZMod N → ℂ)
    {M : ℝ} (ha : ∀ k, ‖ZMod.dft a k‖ ≤ M) :
    ∑ x : ZMod N, ‖∑ y : ZMod N, a (x - y) * b y‖ ^ 2 ≤
      M ^ 2 * ∑ y : ZMod N, ‖b y‖ ^ 2 := by
  have hm : 0 ≤ M := (norm_nonneg _).trans (ha 0)
  have hbnd : ∑ k : ZMod N,
      ‖ZMod.dft (fun x => ∑ y : ZMod N, a (x - y) * b y) k‖ ^ 2 ≤
      M ^ 2 * ∑ k : ZMod N, ‖ZMod.dft b k‖ ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro k _
    rw [dft_convolution, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha k) 2)
      (sq_nonneg _)
  rw [dft_parseval, dft_parseval] at hbnd
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  nlinarith

lemma centered_square_dft_bound {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (k : ZMod p) :
    ‖ZMod.dft (fun x : ZMod p => (squareIndicator x : ℂ) - 1 / 2) k‖ ≤
      (Real.sqrt p + 1) / 2 := by
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  by_cases hk : k = 0
  · subst k
    rw [ZMod.dft_apply_zero, sum_sub_distrib]
    have hs : ∑ x : ZMod p, (squareIndicator x : ℂ) = (p - 1 : ℂ) / 2 := by
      have hsum := squareIndicator_sum hF
      rw [ZMod.card] at hsum
      exact_mod_cast hsum
    rw [hs]
    simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    have heq : (p - 1 : ℂ) / 2 - (p : ℂ) * (1 / 2) = -(1 / 2) := by ring
    rw [heq, norm_neg, norm_div, norm_one]
    norm_num only [Complex.norm_ofNat]
    linarith [Real.sqrt_nonneg (p : ℝ)]
  · let ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar.mulShift (-k)
    have hn : ψ ≠ 1 := ZMod.isPrimitive_stdAddChar p (neg_ne_zero.mpr hk)
    have hψ : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hn
    have hdft : ZMod.dft (fun x : ZMod p => (squareIndicator x : ℂ) - 1 / 2) k =
        ∑ x : ZMod p, (squareIndicator x : ℂ) * ψ x := by
      simp only [ZMod.dft_apply, smul_eq_mul, mul_sub, sum_sub_distrib]
      have heq (x : ZMod p) : ZMod.stdAddChar (-(x * k)) = ψ x := by
        simp [ψ, AddChar.mulShift_apply, mul_comm]
      simp_rw [heq]
      rw [← sum_mul, AddChar.sum_eq_zero_of_ne_one hn, zero_mul, sub_zero]
      apply sum_congr rfl
      intro x _
      exact mul_comm _ _
    rw [hdft]
    simpa only [ZMod.card] using squareIndicator_char_sum_norm hF hψ

lemma centered_square_convolution_l2 {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f : ZMod p → ℝ) :
    ∑ x : ZMod p, (∑ y : ZMod p, (squareIndicator (x - y) - 1 / 2) * f y) ^ 2 ≤
      ((Real.sqrt p + 1) / 2) ^ 2 * ∑ y : ZMod p, (f y) ^ 2 := by
  have h := convolution_l2_sq_le
    (fun x : ZMod p => (squareIndicator x : ℂ) - 1 / 2)
    (fun x : ZMod p => (f x : ℂ)) (centered_square_dft_bound hp)
  have hsum (x : ZMod p) :
      ∑ y : ZMod p, ((squareIndicator (x - y) : ℂ) - 1 / 2) * (f y : ℂ) =
        ((∑ y : ZMod p, (squareIndicator (x - y) - 1 / 2) * f y : ℝ) : ℂ) := by
    push_cast
    rfl
  simp_rw [hsum, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h

lemma single_square_mixing_unnormalized {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f g : ZMod p → ℝ) :
    |∑ x : ZMod p, ∑ y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)| ≤
      ((Real.sqrt p + 1) / 2) * Real.sqrt (∑ x : ZMod p, (f x) ^ 2) *
        Real.sqrt (∑ y : ZMod p, (g y) ^ 2) := by
  let c (y : ZMod p) := ∑ x : ZMod p, (squareIndicator (y - x) - 1 / 2) * f x
  have hc := centered_square_convolution_l2 hp f
  have hcs := sum_mul_sq_le_sq_mul_sq univ g c
  have hf : 0 ≤ ∑ x : ZMod p, (f x) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hg : 0 ≤ ∑ y : ZMod p, (g y) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hM : 0 ≤ (Real.sqrt (p : ℝ) + 1) / 2 := by positivity
  have hbnd : (∑ y : ZMod p, g y * c y) ^ 2 ≤
      (((Real.sqrt p + 1) / 2) * Real.sqrt (∑ x : ZMod p, (f x) ^ 2) *
        Real.sqrt (∑ y : ZMod p, (g y) ^ 2)) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt hf, Real.sq_sqrt hg]
    calc
      _ ≤ (∑ y : ZMod p, (g y) ^ 2) * (∑ y : ZMod p, (c y) ^ 2) := hcs
      _ ≤ (∑ y : ZMod p, (g y) ^ 2) *
          (((Real.sqrt p + 1) / 2) ^ 2 * ∑ x : ZMod p, (f x) ^ 2) :=
        mul_le_mul_of_nonneg_left hc hg
      _ = _ := by ring
  have heq : (∑ x : ZMod p, ∑ y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)) =
      ∑ y : ZMod p, g y * c y := by
    rw [sum_comm]
    simp only [c, mul_sum]
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro x _
    ring
  rw [heq]
  exact abs_le_of_sq_le_sq hbnd (mul_nonneg (mul_nonneg hM (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _))

lemma single_square_mixing_bounded {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f g : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1) :
    |(∑ x : ZMod p, ∑ y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)) / (p : ℝ) ^ 2| ≤
      (Real.sqrt p + 1) / (2 * p) := by
  have hnp : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos Fact.out)
  have hfp : ∑ x : ZMod p, (f x) ^ 2 ≤ (p : ℝ) := by
    calc
      _ ≤ ∑ _x : ZMod p, (1 : ℝ) := sum_le_sum (fun x _ => by
        have := (sq_le_sq₀ (abs_nonneg (f x)) zero_le_one).mpr (hf x)
        simpa only [sq_abs, one_pow] using this)
      _ = _ := by simp
  have hgp : ∑ x : ZMod p, (g x) ^ 2 ≤ (p : ℝ) := by
    calc
      _ ≤ ∑ _x : ZMod p, (1 : ℝ) := sum_le_sum (fun x _ => by
        have := (sq_le_sq₀ (abs_nonneg (g x)) zero_le_one).mpr (hg x)
        simpa only [sq_abs, one_pow] using this)
      _ = _ := by simp
  have h := single_square_mixing_unnormalized hp f g
  have hh : |∑ x : ZMod p, ∑ y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)| ≤
      ((Real.sqrt p + 1) / 2) * p := by
    calc
      _ ≤ _ := h
      _ ≤ ((Real.sqrt p + 1) / 2) * Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) := by
        gcongr
      _ = _ := by rw [mul_assoc, ← pow_two, Real.sq_sqrt hnp.le]
  rw [abs_div, abs_of_pos (pow_pos hnp 2)]
  calc
    _ ≤ (((Real.sqrt p + 1) / 2) * p) / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hh (by positivity)
    _ = _ := by field_simp

lemma expect_update {W X : Type*} [Fintype W] [Fintype X] [Nonempty X]
    [DecidableEq W] (u : W) (H : (W → X) → ℝ) :
    (𝔼 z : W → X, 𝔼 x : X, H (Function.update z u x)) = 𝔼 z : W → X, H z := by
  let e : ((W → X) × X) ≃ ((W → X) × X) :=
    { toFun := fun a => (Function.update a.1 u a.2, a.1 u)
      invFun := fun a => (Function.update a.1 u a.2, a.1 u)
      left_inv := by rintro ⟨z, x⟩; simp
      right_inv := by rintro ⟨z, x⟩; simp }
  have he := Fintype.expect_equiv e
    (fun a : (W → X) × X => H (Function.update a.1 u a.2))
    (fun a : (W → X) × X => H a.1) (fun _ => rfl)
  rw [← univ_product_univ, expect_product, expect_product] at he
  simpa only [expect_const univ_nonempty] using he

lemma expect_update_two {W X : Type*} [Fintype W] [Fintype X] [Nonempty X]
    [DecidableEq W] (u v : W) (H : (W → X) → ℝ) :
    (𝔼 z : W → X, 𝔼 x : X, 𝔼 y : X,
      H (Function.update (Function.update z u x) v y)) = 𝔼 z : W → X, H z := by
  calc
    _ = 𝔼 z : W → X, 𝔼 y : X, H (Function.update z v y) :=
      expect_update u (fun z => 𝔼 y : X, H (Function.update z v y))
    _ = _ := expect_update v H

lemma single_square_mixing_expect {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f g : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1) :
    |𝔼 x : ZMod p, 𝔼 y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)| ≤
      (Real.sqrt p + 1) / (2 * p) := by
  have h := single_square_mixing_bounded hp f g hf hg
  simpa only [Fintype.expect_eq_sum_div_card, ZMod.card, ← sum_div, div_div,
    ← pow_two] using h

lemma edge_product_factor {W X : Type*} [DecidableEq W]
    (E : Finset (W × W)) (A : X → X → ℝ) {u v : W} (huv : u ≠ v)
    (he : ∀ e ∈ E, ¬ ((e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u)))
    (z : W → X) (x y : X) :
    (∏ e ∈ E, A ((Function.update (Function.update z u x) v y) e.1)
        ((Function.update (Function.update z u x) v y) e.2)) =
      (∏ e ∈ E, if e.1 = v ∨ e.2 = v then 1 else
        A ((Function.update z u x) e.1) ((Function.update z u x) e.2)) *
      (∏ e ∈ E, if e.1 = v ∨ e.2 = v then
        A ((Function.update z v y) e.1) ((Function.update z v y) e.2) else 1) := by
  classical
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro e heE
  by_cases hv : e.1 = v ∨ e.2 = v
  · have hne1 : e.1 ≠ u := by
      have := he e heE
      aesop
    have hne2 : e.2 ≠ u := by
      have := he e heE
      aesop
    simp [hv, Function.update_apply, hne1, hne2]
  · have hv1 := (not_or.mp hv).1
    have hv2 := (not_or.mp hv).2
    simp [Function.update_apply, hv1, hv2]

lemma edge_product_abs_le_one {W X : Type*} (E : Finset (W × W))
    (A : X → X → ℝ) (hA0 : ∀ x y, 0 ≤ A x y) (hA1 : ∀ x y, A x y ≤ 1)
    (z : W → X) : |∏ e ∈ E, A (z e.1) (z e.2)| ≤ 1 := by
  rw [abs_of_nonneg (prod_nonneg (fun _ _ => hA0 _ _))]
  exact prod_le_one₀ (fun _ _ => hA0 _ _) (fun _ _ => hA1 _ _)

lemma graph_edge_error {W X : Type*} [Fintype W] [Fintype X] [Nonempty X]
    [DecidableEq W] (E : Finset (W × W)) (A : X → X → ℝ)
    (hA0 : ∀ x y, 0 ≤ A x y) (hA1 : ∀ x y, A x y ≤ 1)
    {δ : ℝ} (hmix : ∀ f g : X → ℝ, (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) →
      |𝔼 x : X, 𝔼 y : X, f x * g y * (A x y - 1 / 2)| ≤ δ)
    {u v : W} (huv : u ≠ v)
    (he : ∀ e ∈ E, ¬ ((e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u))) :
    |𝔼 z : W → X, (A (z u) (z v) - 1 / 2) * ∏ e ∈ E, A (z e.1) (z e.2)| ≤ δ := by
  classical
  let F (z : W → X) (x : X) := ∏ e ∈ E, if e.1 = v ∨ e.2 = v then 1 else
    A ((Function.update z u x) e.1) ((Function.update z u x) e.2)
  let G (z : W → X) (y : X) := ∏ e ∈ E, if e.1 = v ∨ e.2 = v then
    A ((Function.update z v y) e.1) ((Function.update z v y) e.2) else 1
  have hF (z : W → X) (x : X) : |F z x| ≤ 1 := by
    dsimp [F]
    rw [abs_prod]
    apply prod_le_one₀ (fun _ _ => abs_nonneg _)
    intro e _
    split_ifs
    · norm_num
    · rw [abs_of_nonneg (hA0 _ _)]
      exact hA1 _ _
  have hG (z : W → X) (y : X) : |G z y| ≤ 1 := by
    dsimp [G]
    rw [abs_prod]
    apply prod_le_one₀ (fun _ _ => abs_nonneg _)
    intro e _
    split_ifs
    · rw [abs_of_nonneg (hA0 _ _)]
      exact hA1 _ _
    · norm_num
  let H (z : W → X) := (A (z u) (z v) - 1 / 2) * ∏ e ∈ E, A (z e.1) (z e.2)
  have hH (z : W → X) (x y : X) :
      H (Function.update (Function.update z u x) v y) =
        F z x * G z y * (A x y - 1 / 2) := by
    dsimp [H, F, G]
    rw [edge_product_factor E A huv he]
    simp only [Function.update_of_ne huv, Function.update_self]
    ring
  change |𝔼 z : W → X, H z| ≤ δ
  rw [← expect_update_two u v H]
  simp_rw [hH]
  calc
    _ ≤ 𝔼 z : W → X, |𝔼 x : X, 𝔼 y : X,
        F z x * G z y * (A x y - 1 / 2)| := abs_expect_le _ _
    _ ≤ δ := expect_le univ_nonempty (fun z _ => hmix (F z) (G z) (hF z) (hG z))

lemma graph_counting {W X : Type*} [Fintype W] [Fintype X] [Nonempty X]
    [DecidableEq W] (E : Finset (W × W)) (A : X → X → ℝ)
    (hA0 : ∀ x y, 0 ≤ A x y) (hA1 : ∀ x y, A x y ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmix : ∀ f g : X → ℝ, (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) →
      |𝔼 x : X, 𝔼 y : X, f x * g y * (A x y - 1 / 2)| ≤ δ)
    (hnoloop : ∀ e ∈ E, e.1 ≠ e.2)
    (hnoopp : ∀ e ∈ E, (e.2, e.1) ∉ E) :
    |(𝔼 z : W → X, ∏ e ∈ E, A (z e.1) (z e.2)) - (1 / 2 : ℝ) ^ E.card| ≤
      E.card * δ := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | @insert e E hne ih =>
    have hloop := hnoloop e (mem_insert_self e E)
    have hcross : ∀ a ∈ E, ¬ ((a.1 = e.1 ∧ a.2 = e.2) ∨
        (a.1 = e.2 ∧ a.2 = e.1)) := by
      intro a ha h
      rcases h with h | h
      · have hae : a = e := Prod.ext h.1 h.2
        exact hne (hae ▸ ha)
      · have hae : a = (e.2, e.1) := Prod.ext h.1 h.2
        exact hnoopp e (mem_insert_self e E) (mem_insert_of_mem (hae ▸ ha))
    have herr := graph_edge_error E A hA0 hA1 hmix hloop hcross
    have hind := ih (fun a ha => hnoloop a (mem_insert_of_mem ha))
      (fun a ha hop => hnoopp a (mem_insert_of_mem ha) (mem_insert_of_mem hop))
    let S : ℝ := 𝔼 z : W → X, ∏ a ∈ E, A (z a.1) (z a.2)
    let R : ℝ := 𝔼 z : W → X,
      (A (z e.1) (z e.2) - 1 / 2) * ∏ a ∈ E, A (z a.1) (z a.2)
    have heq : (𝔼 z : W → X, ∏ a ∈ insert e E, A (z a.1) (z a.2)) =
        R + (1 / 2) * S := by
      dsimp [R, S]
      simp only [prod_insert hne, sub_mul, expect_sub_distrib, ← mul_expect]
      ring
    rw [heq, card_insert_of_notMem hne, pow_succ, Nat.cast_add, Nat.cast_one]
    have hrewrite : R + 1 / 2 * S - (1 / 2 : ℝ) ^ E.card * (1 / 2) =
        R + 1 / 2 * (S - (1 / 2 : ℝ) ^ E.card) := by ring
    rw [hrewrite]
    calc
      _ ≤ |R| + |1 / 2 * (S - (1 / 2 : ℝ) ^ E.card)| := abs_add_le _ _
      _ = |R| + 1 / 2 * |S - (1 / 2 : ℝ) ^ E.card| := by
        rw [abs_mul]
        norm_num
      _ ≤ δ + 1 / 2 * (E.card * δ) := add_le_add herr (mul_le_mul_of_nonneg_left hind (by norm_num))
      _ ≤ (E.card + 1) * δ := by nlinarith [mul_nonneg (Nat.cast_nonneg E.card) hδ]

lemma graph_count {W : Type*} [Fintype W] [DecidableEq W]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (E : Finset (W × W))
    (hnoloop : ∀ e ∈ E, e.1 ≠ e.2) (hnoopp : ∀ e ∈ E, (e.2, e.1) ∉ E) :
    |(𝔼 z : W → ZMod p, ∏ e ∈ E, squareIndicator (z e.2 - z e.1)) -
      (1 / 2 : ℝ) ^ E.card| ≤ E.card * ((Real.sqrt p + 1) / (2 * p)) := by
  exact graph_counting E (fun x y : ZMod p => squareIndicator (y - x))
    (fun _ _ => squareIndicator_nonneg _) (fun _ _ => squareIndicator_le_one _)
    (by positivity) (single_square_mixing_expect hp) hnoloop hnoopp

lemma four_cycle_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (B : X → Y → ℝ) (f : X → ℝ) (g : Y → ℝ) :
    (𝔼 x : X, 𝔼 y : Y, f x * B x y * g y) ^ 4 ≤
      (𝔼 x : X, 𝔼 x' : X, 𝔼 y : Y, 𝔼 y' : Y,
        B x y * B x y' * B x' y * B x' y') *
      (𝔼 x : X, (f x) ^ 2) ^ 2 * (𝔼 y : Y, (g y) ^ 2) ^ 2 := by
  classical
  let T (x : X) := 𝔼 y : Y, B x y * g y
  let C (y y' : Y) := 𝔼 x : X, B x y * B x y'
  have h1 := expect_mul_sq_le_sq_mul_sq univ f T
  have h2 := expect_mul_sq_le_sq_mul_sq (univ : Finset (Y × Y))
    (fun yy => g yy.1 * g yy.2) (fun yy => C yy.1 yy.2)
  have hT : (𝔼 x : X, (T x) ^ 2) =
      𝔼 yy : Y × Y, (g yy.1 * g yy.2) * C yy.1 yy.2 := by
    rw [← univ_product_univ, expect_product]
    dsimp [T, C]
    simp_rw [sq, expect_mul, mul_expect]
    rw [expect_comm]
    congr 1
    ext y
    rw [expect_comm]
    congr 1
    ext y'
    apply expect_congr rfl
    intro x _
    ring
  have hgg : (𝔼 yy : Y × Y, (g yy.1 * g yy.2) ^ 2) =
      (𝔼 y : Y, (g y) ^ 2) ^ 2 := by
    rw [← univ_product_univ, expect_product]
    simp_rw [mul_pow, ← mul_expect, ← expect_mul]
    ring
  have hC : (𝔼 yy : Y × Y, (C yy.1 yy.2) ^ 2) =
      𝔼 x : X, 𝔼 x' : X, 𝔼 y : Y, 𝔼 y' : Y,
        B x y * B x y' * B x' y * B x' y' := by
    rw [← univ_product_univ, expect_product]
    dsimp [C]
    simp_rw [sq, expect_mul, mul_expect]
    rw [expect_comm]
    simp_rw [expect_comm (univ : Finset Y) (univ : Finset X)]
    rw [expect_comm]
    apply expect_congr rfl
    intro x _
    apply expect_congr rfl
    intro x' _
    apply expect_congr rfl
    intro y _
    apply expect_congr rfl
    intro y' _
    ring
  rw [hgg, hC, ← hT] at h2
  have hF : 0 ≤ 𝔼 x : X, (f x) ^ 2 := expect_nonneg (fun _ _ => sq_nonneg _)
  have hT0 : 0 ≤ 𝔼 x : X, (T x) ^ 2 := expect_nonneg (fun _ _ => sq_nonneg _)
  have hrewrite : (𝔼 x : X, 𝔼 y : Y, f x * B x y * g y) =
      𝔼 x : X, f x * T x := by
    dsimp [T]
    simp_rw [mul_expect, mul_assoc]
  rw [hrewrite, show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  calc
    _ ≤ ((𝔼 x : X, (f x) ^ 2) * (𝔼 x : X, (T x) ^ 2)) ^ 2 :=
      (sq_le_sq₀ (sq_nonneg _) (mul_nonneg hF hT0)).mpr h1
    _ = (𝔼 x : X, (f x) ^ 2) ^ 2 * (𝔼 x : X, (T x) ^ 2) ^ 2 := mul_pow _ _ _
    _ ≤ (𝔼 x : X, (f x) ^ 2) ^ 2 *
        ((𝔼 y : Y, (g y) ^ 2) ^ 2 *
          (𝔼 x : X, 𝔼 x' : X, 𝔼 y : Y, 𝔼 y' : Y,
            B x y * B x y' * B x' y * B x' y')) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

end SquareDifference
end

end OAI
