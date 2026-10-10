import Mathlib

namespace OAI

namespace MetricKMedianRecovery.RadiusMenus

noncomputable def firstSize (kappa : ℝ) : ℕ := Nat.ceil (10/kappa)+1
noncomputable def thirdSize (kappa : ℝ) (m : ℕ) : ℕ := 1+Nat.ceil (2*m/kappa)
noncomputable def upwardIndex (kappa q r : ℝ) : ℕ := max 1 (Nat.ceil (r/(kappa*q)))
noncomputable def additiveRadius (kappa q : ℝ) (j : ℕ) : ℝ := j*kappa*q

lemma additiveRadius_pos (kappa q : ℝ) (j : ℕ) (hk : 0 < kappa)
    (hq : 0 < q) (hj : 0 < j) : 0 < additiveRadius kappa q j := by
  exact mul_pos (mul_pos (Nat.cast_pos.mpr hj) hk) hq

lemma upward_radius_bounds (kappa q r : ℝ) (hk : 0 < kappa) (hq : 0 < q)
    (hr : 0 ≤ r) :
    r ≤ additiveRadius kappa q (upwardIndex kappa q r) ∧
      additiveRadius kappa q (upwardIndex kappa q r) ≤ r+kappa*q := by
  have hkq : 0 < kappa*q := mul_pos hk hq
  have hcast : (upwardIndex kappa q r : ℝ) = max 1 (Nat.ceil (r/(kappa*q)) : ℝ) := by
    simp only [upwardIndex, Nat.cast_max, Nat.cast_one]
  have hlow : r/(kappa*q) ≤ (upwardIndex kappa q r : ℝ) := by
    rw [hcast]
    exact (Nat.le_ceil _).trans (le_max_right _ _)
  have hu := Nat.ceil_lt_add_one_of_gt_neg_one (show (-1 : ℝ) < r/(kappa*q) by
    have := div_nonneg hr hkq.le
    linarith)
  have hu' : (upwardIndex kappa q r : ℝ) ≤ r/(kappa*q)+1 := by
    rw [hcast]
    exact max_le (by have := div_nonneg hr hkq.le; linarith) hu.le
  constructor
  · have hh := (div_le_iff₀ hkq).mp hlow
    simpa only [additiveRadius, mul_assoc] using hh
  · have hh := mul_le_mul_of_nonneg_right hu' hkq.le
    have he : (r/(kappa*q)+1)*(kappa*q) = r+kappa*q := by field_simp
    rw [he] at hh
    simpa only [additiveRadius, mul_assoc] using hh

lemma first_menu_available (kappa q r : ℝ) (hk : 0 < kappa) (hq : 0 < q)
    (hr : 0 ≤ r) (hsmall : r ≤ 10*q) :
    1 ≤ upwardIndex kappa q r ∧ upwardIndex kappa q r ≤ firstSize kappa ∧
      r ≤ additiveRadius kappa q (upwardIndex kappa q r) ∧
      additiveRadius kappa q (upwardIndex kappa q r) ≤ (1+kappa)*r+kappa*q := by
  have hrq : r/(kappa*q) ≤ 10/kappa := by
    apply (div_le_div_iff₀ (mul_pos hk hq) hk).mpr
    nlinarith
  have hceil := Nat.ceil_mono hrq
  have hbound : upwardIndex kappa q r ≤ firstSize kappa := by
    unfold upwardIndex firstSize
    omega
  have hb := upward_radius_bounds kappa q r hk hq hr
  exact ⟨le_max_left _ _, hbound, hb.1, hb.2.trans (by nlinarith [mul_nonneg hk.le hr])⟩

lemma third_menu_available (kappa q r : ℝ) (m : ℕ) (hk : 0 < kappa)
    (hq : 0 < q) (hr : 0 < r) (hbudget : r/q ≤ (10/9 : ℝ)*m) :
    1 ≤ Nat.ceil (r/(kappa*q)) ∧ Nat.ceil (r/(kappa*q)) ≤ thirdSize kappa m ∧
      r ≤ additiveRadius kappa q (Nat.ceil (r/(kappa*q))) ∧
      additiveRadius kappa q (Nat.ceil (r/(kappa*q))) ≤ (1+kappa)*r+kappa*q := by
  have hj : 0 < Nat.ceil (r/(kappa*q)) := Nat.ceil_pos.mpr (div_pos hr (mul_pos hk hq))
  have he : r/(kappa*q) = (r/q)/kappa := by ring
  have hratio : r/(kappa*q) ≤ 2*m/kappa := by
    rw [he]
    apply div_le_div_of_nonneg_right _ hk.le
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hm := Nat.ceil_mono hratio
  have hidx : upwardIndex kappa q r = Nat.ceil (r/(kappa*q)) := max_eq_right hj
  have hu := upward_radius_bounds kappa q r hk hq hr.le
  rw [hidx] at hu
  refine ⟨hj, ?_, hu.1, hu.2.trans ?_⟩
  · dsimp [thirdSize]
    omega
  · nlinarith [mul_nonneg hk.le hr.le]

lemma geometric_exists (kappa : ℝ) (hk : 0 < kappa) : ∃ e : ℕ, 10 ≤ (1+kappa)^e := by
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt (10 : ℝ) (show 1 < 1+kappa by linarith)
  exact ⟨e, he.le⟩

noncomputable def geometricCap (kappa : ℝ) (hk : 0 < kappa) : ℕ :=
  Nat.find (geometric_exists kappa hk)

lemma geometricCap_spec (kappa : ℝ) (hk : 0 < kappa) :
    10 ≤ (1+kappa)^(geometricCap kappa hk) := Nat.find_spec (geometric_exists kappa hk)

lemma geometric_menu_available (kappa D r : ℝ) (hk : 0 < kappa)
    (hr : 0 < r) (hlow : r ≤ D) (hupp : D ≤ 10*r) :
    ∃ e ≤ geometricCap kappa hk,
      r ≤ D/(1+kappa)^e ∧ D/(1+kappa)^e ≤ (1+kappa)*r := by
  have hb : 1 < 1+kappa := by linarith
  have hratio : 1 ≤ D/r := (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hlow)
  obtain ⟨e, he₀, he₁⟩ := exists_nat_pow_near hratio hb
  have hpow : 0 < (1+kappa)^e := pow_pos (by linarith) _
  have heE : e ≤ geometricCap kappa hk := by
    by_contra hh
    have hegt : geometricCap kappa hk < e := lt_of_not_ge hh
    have hn := pow_lt_pow_right₀ hb hegt
    have hcap := geometricCap_spec kappa hk
    have hratio' : D/r ≤ 10 := (div_le_iff₀ hr).mpr hupp
    linarith
  refine ⟨e, heE, ?_, ?_⟩
  · apply (le_div_iff₀ hpow).mpr
    have hh := (le_div_iff₀ hr).mp he₀
    nlinarith
  · apply (div_le_iff₀ hpow).mpr
    have hh := (div_lt_iff₀ hr).mp he₁
    rw [pow_succ] at hh
    nlinarith

noncomputable def thirdNormalizer (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, (1/2 : ℝ)^(j+1)

lemma thirdNormalizer_eq (J : ℕ) :
    thirdNormalizer J = 1-(1/2 : ℝ)^J := by
  induction J with
  | zero => simp [thirdNormalizer]
  | succ J ih =>
    rw [thirdNormalizer, Finset.sum_range_succ, ← thirdNormalizer, ih, pow_succ]
    ring

lemma thirdNormalizer_pos {J : ℕ} (hJ : 0 < J) : 0 < thirdNormalizer J := by
  rw [thirdNormalizer_eq]
  have hh : (1/2 : ℝ)^J < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  linarith

lemma thirdNormalizer_lt_one (J : ℕ) : thirdNormalizer J < 1 := by
  rw [thirdNormalizer_eq]
  have hh : (0 : ℝ) < (1/2 : ℝ)^J := pow_pos (by norm_num) _
  linarith

noncomputable def menuConstant (kappa : ℝ) (hk : 0 < kappa) : ℝ :=
  min (1/(3*(firstSize kappa : ℝ)))
    (min (1/(3*((geometricCap kappa hk : ℝ)+1))) (1/3))

lemma menuConstant_pos (kappa : ℝ) (hk : 0 < kappa) : 0 < menuConstant kappa hk := by
  have hM : (0 : ℝ) < firstSize kappa := by
    dsimp [firstSize]
    positivity
  unfold menuConstant
  refine lt_min (div_pos zero_lt_one (mul_pos (by norm_num) hM)) ?_
  exact lt_min (by positivity) (by norm_num)

lemma menuConstant_le_one (kappa : ℝ) (hk : 0 < kappa) : menuConstant kappa hk ≤ 1 := by
  exact ((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num)

lemma first_entry_lower (kappa : ℝ) (hk : 0 < kappa) :
    menuConstant kappa hk ≤ 1/(3*(firstSize kappa : ℝ)) := min_le_left _ _

lemma second_entry_lower (kappa : ℝ) (hk : 0 < kappa) :
    menuConstant kappa hk ≤ 1/(3*((geometricCap kappa hk : ℝ)+1)) :=
  (min_le_right _ _).trans (min_le_left _ _)

lemma third_entry_lower (kappa : ℝ) (hk : 0 < kappa) (J j : ℕ) (hJ : 0 < J) :
    menuConstant kappa hk * (1/2 : ℝ)^j ≤
      (1/3 : ℝ) * ((1/2 : ℝ)^j / thirdNormalizer J) := by
  have hc : menuConstant kappa hk ≤ 1/3 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hp : (0 : ℝ) ≤ (1/2 : ℝ)^j := pow_nonneg (by norm_num) _
  have hh : (1/2 : ℝ)^j ≤ (1/2 : ℝ)^j / thirdNormalizer J := by
    apply (le_div_iff₀ (thirdNormalizer_pos hJ)).mpr
    exact mul_le_of_le_one_right hp (thirdNormalizer_lt_one J).le
  exact (mul_le_mul_of_nonneg_right hc hp).trans
    (mul_le_mul_of_nonneg_left hh (by norm_num))

noncomputable def menuWeight (M E J : ℕ) : Fin M ⊕ (Fin (E+1) ⊕ Fin J) → ℝ
  | .inl _ => 1/(3*M)
  | .inr (.inl _) => 1/(3*(E+1))
  | .inr (.inr j) => (1/3) * ((1/2 : ℝ)^(j.val+1)/thirdNormalizer J)

lemma menuWeight_total (M E J : ℕ) (hM : 0 < M) (hJ : 0 < J) :
    ∑ x, menuWeight M E J x = 1 := by
  have hMr : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hEr : (E : ℝ)+1 ≠ 0 := by positivity
  have hJr : thirdNormalizer J ≠ 0 := ne_of_gt (thirdNormalizer_pos hJ)
  simp only [Fintype.sum_sum_type, menuWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (1/2 : ℝ)^(j+1)) J]
  change (M : ℝ)*(1/(3*M)) +
    (((E+1 : ℕ) : ℝ)*(1/(3*((E : ℝ)+1))) +
      (1/3)*(thirdNormalizer J/thirdNormalizer J)) = 1
  rw [div_self hJr]
  push_cast
  field_simp
  ring

theorem menu_product_budget {ι : Type*} (s : Finset ι) (m : ℕ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (j : ι → ℕ) (p : ι → ℝ)
    (hp : ∀ i ∈ s, c*(1/2 : ℝ)^(j i) ≤ p i)
    (hn : s.card ≤ m) (A : ℝ) (hA : (∑ i ∈ s, (j i : ℝ)) ≤ A) :
    c^m * (2 : ℝ)^(-A) ≤ ∏ i ∈ s, p i := by
  have hcp : c^m ≤ c^s.card := pow_le_pow_of_le_one hc.le hc1 hn
  have hsum : (2 : ℝ)^(-A) ≤ (1/2 : ℝ)^(∑ i ∈ s, j i) := by
    rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hprod : c^s.card * (1/2 : ℝ)^(∑ i ∈ s, j i) =
      ∏ i ∈ s, c*(1/2 : ℝ)^(j i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← Finset.prod_pow_eq_pow_sum]
  calc
    _ ≤ c^s.card*(1/2 : ℝ)^(∑ i ∈ s, j i) :=
      mul_le_mul hcp hsum (Real.rpow_nonneg (by norm_num) _) (pow_nonneg hc.le _)
    _ = _ := hprod
    _ ≤ _ := Finset.prod_le_prod₀ (fun index _ => mul_nonneg hc.le (pow_nonneg (by norm_num) (j index))) hp

end MetricKMedianRecovery.RadiusMenus

end OAI
