import Mathlib

namespace OAI

namespace IndependentSetsGames.Foundations.Information

section

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsProbability (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

def SupportedBy (p q : α → ℝ) : Prop := ∀ a, p a ≠ 0 → q a ≠ 0

noncomputable def relativeEntropy (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

noncomputable def totalVariation (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

noncomputable def posterior (p w : α → ℝ) (z : ℝ) : α → ℝ :=
  fun a => p a * w a / z

theorem posterior_isProbability (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) : IsProbability (posterior p w z) := by
  constructor
  · intro a
    exact div_nonneg (mul_nonneg (hp.1 a) (hw a)) hz.le
  · simp only [posterior, div_eq_mul_inv, ← Finset.sum_mul, hmass,
      mul_inv_cancel₀ hz.ne']

omit [Fintype α] in
theorem posterior_supportedBy (p w : α → ℝ) (z : ℝ) :
    SupportedBy (posterior p w z) p := by
  intro a ha hp
  exact ha (by simp [posterior, hp])

theorem mul_log_div_ge_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * Real.log (x / y) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
  have hm := mul_le_mul_of_nonneg_left h hx.le
  have he : x * (1 - (x / y)⁻¹) = x - y := by
    field_simp [hx.ne', hy.ne']
  rwa [he] at hm

theorem relativeEntropy_nonneg (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) : 0 ≤ relativeEntropy p q := by
  have hpoint : ∀ a, p a - q a ≤ p a * Real.log (p a / q a) := by
    intro a
    by_cases hpa : p a = 0
    · simp only [hpa, zero_sub, zero_div, zero_mul]
      exact neg_nonpos.mpr (hq.1 a)
    · exact mul_log_div_ge_sub (lt_of_le_of_ne (hp.1 a) (Ne.symm hpa))
        (lt_of_le_of_ne (hq.1 a) (Ne.symm (hs a hpa)))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa [relativeEntropy, Finset.sum_sub_distrib, hp.2, hq.2] using hsum

theorem posterior_relativeEntropy_le (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) (hw_one : ∀ a, w a ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) :
    relativeEntropy (posterior p w z) p ≤ Real.log (1 / z) := by
  have hpost := posterior_isProbability p w hp hw hz hmass
  have hpoint : ∀ a, posterior p w z a * Real.log (posterior p w z a / p a) ≤
      posterior p w z a * Real.log (1 / z) := by
    intro a
    by_cases hpa : posterior p w z a = 0
    · simp [hpa]
    have hpne := posterior_supportedBy p w z a hpa
    have hppos : 0 < p a := lt_of_le_of_ne (hp.1 a) (Ne.symm hpne)
    have hpostpos : 0 < posterior p w z a :=
      lt_of_le_of_ne (hpost.1 a) (Ne.symm hpa)
    have hr : posterior p w z a / p a = w a / z := by
      dsimp [posterior]
      field_simp [hpne, hz.ne']
    apply mul_le_mul_of_nonneg_left _ (hpost.1 a)
    apply Real.log_le_log (div_pos hpostpos hppos)
    rw [hr]
    exact div_le_div_of_nonneg_right (hw_one a) hz.le
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa only [relativeEntropy, ← Finset.sum_mul, hpost.2, one_mul] using hsum

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => abs_nonneg (p a - q a))) (by norm_num)

theorem totalVariation_symm (p q : α → ℝ) : totalVariation p q = totalVariation q p := by
  simp only [totalVariation, abs_sub_comm]

theorem totalVariation_le_one (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) : totalVariation p q ≤ 1 := by
  have hpoint : ∀ a, |p a - q a| ≤ p a + q a := by
    intro a
    rw [abs_le]
    constructor <;> linarith [hp.1 a, hq.1 a]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [Finset.sum_add_distrib, hp.2, hq.2] at hsum
  dsimp [totalVariation]
  linarith

theorem le_binaryLog_of_le_log {r x : ℝ} (hr : 0 ≤ r) (h : r ≤ Real.log x) :
    r ≤ Real.log x / Real.log 2 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo_one : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    exact ht
  apply (le_div_iff₀ htwo).2
  exact (mul_le_mul_of_nonneg_left htwo_one hr).trans (by simpa using h)

theorem weighted_sum_sq_le (w x : α → ℝ) (hw : IsProbability w) :
    (∑ a, w a * x a)^2 ≤ ∑ a, w a * (x a)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => Real.sqrt (w a)) (fun a => Real.sqrt (w a) * x a)
  have hfirst : ∀ a, Real.sqrt (w a) * (Real.sqrt (w a) * x a) = w a * x a := by
    intro a
    rw [← mul_assoc, Real.mul_self_sqrt (hw.1 a)]
  have hsecond : ∀ a, (Real.sqrt (w a) * x a)^2 = w a * (x a)^2 := by
    intro a
    rw [mul_pow, Real.sq_sqrt (hw.1 a)]
  simpa only [hfirst, hsecond, Real.sq_sqrt (hw.1 _), hw.2, one_mul] using hcs

end

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def firstMarginal (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)

noncomputable def secondMarginal (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)

def product (p : α → ℝ) (q : β → ℝ) : α × β → ℝ := fun ab => p ab.1 * q ab.2

theorem firstMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (firstMarginal p) := by
  constructor
  · intro a
    exact Finset.sum_nonneg (fun b _ => hp.1 (a, b))
  · simpa only [firstMarginal, Fintype.sum_prod_type] using hp.2

theorem secondMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (secondMarginal p) := by
  constructor
  · intro b
    exact Finset.sum_nonneg (fun a _ => hp.1 (a, b))
  · change (∑ b, ∑ a, p (a, b)) = 1
    rw [Finset.sum_comm]
    exact (firstMarginal_isProbability p hp).2

theorem product_isProbability (p : α → ℝ) (q : β → ℝ)
    (hp : IsProbability p) (hq : IsProbability q) : IsProbability (product p q) := by
  constructor
  · intro ab
    exact mul_nonneg (hp.1 ab.1) (hq.1 ab.2)
  · simp only [product, Fintype.sum_prod_type, ← Finset.mul_sum, hq.2, mul_one, hp.2]

theorem point_le_firstMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ firstMarginal p a := by
  classical
  exact Finset.single_le_sum (fun b _ => hp.1 (a, b)) (Finset.mem_univ b)

theorem point_le_secondMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ secondMarginal p b := by
  classical
  exact Finset.single_le_sum (fun a _ => hp.1 (a, b)) (Finset.mem_univ a)

theorem joint_supportedBy_product_marginals (p : α × β → ℝ) (hp : IsProbability p) :
    SupportedBy p (product (firstMarginal p) (secondMarginal p)) := by
  intro ab hpne
  have hpos : 0 < p ab := lt_of_le_of_ne (hp.1 ab) (Ne.symm hpne)
  exact mul_ne_zero
    (ne_of_gt (hpos.trans_le (point_le_firstMarginal p hp ab.1 ab.2)))
    (ne_of_gt (hpos.trans_le (point_le_secondMarginal p hp ab.1 ab.2)))

theorem relativeEntropy_product_reference (p : α × β → ℝ) (u : α → ℝ) (v : β → ℝ)
    (hp : IsProbability p) (hu : IsProbability u) (hv : IsProbability v)
    (hsu : SupportedBy (firstMarginal p) u) (hsv : SupportedBy (secondMarginal p) v) :
    relativeEntropy p (product u v) =
      relativeEntropy p (product (firstMarginal p) (secondMarginal p)) +
        relativeEntropy (firstMarginal p) u + relativeEntropy (secondMarginal p) v := by
  have hpoint : ∀ ab : α × β, p ab * Real.log (p ab / product u v ab) =
      p ab * Real.log (p ab / product (firstMarginal p) (secondMarginal p) ab) +
      p ab * Real.log (firstMarginal p ab.1 / u ab.1) +
      p ab * Real.log (secondMarginal p ab.2 / v ab.2) := by
    intro ab
    by_cases hzero : p ab = 0
    · simp [hzero]
    have hpos : 0 < p ab := lt_of_le_of_ne (hp.1 ab) (Ne.symm hzero)
    have hleft := ne_of_gt (hpos.trans_le (point_le_firstMarginal p hp ab.1 ab.2))
    have hright := ne_of_gt (hpos.trans_le (point_le_secondMarginal p hp ab.1 ab.2))
    have hune := (lt_of_le_of_ne (hu.1 ab.1) (Ne.symm (hsu ab.1 hleft))).ne'
    have hvne := (lt_of_le_of_ne (hv.1 ab.2) (Ne.symm (hsv ab.2 hright))).ne'
    simp only [product, Real.log_div hzero (mul_ne_zero hune hvne),
      Real.log_div hzero (mul_ne_zero hleft hright), Real.log_mul hune hvne,
      Real.log_mul hleft hright, Real.log_div hleft hune, Real.log_div hright hvne]
    ring
  have hleftSum : (∑ ab : α × β, p ab * Real.log (firstMarginal p ab.1 / u ab.1)) =
      relativeEntropy (firstMarginal p) u := by
    simp only [Fintype.sum_prod_type, ← Finset.sum_mul, relativeEntropy, firstMarginal]
  have hrightSum : (∑ ab : α × β, p ab * Real.log (secondMarginal p ab.2 / v ab.2)) =
      relativeEntropy (secondMarginal p) v := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [← Finset.sum_mul, relativeEntropy, secondMarginal]
  unfold relativeEntropy
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hleftSum, hrightSum]
  rfl

theorem marginal_relativeEntropy_sum_le (p : α × β → ℝ) (u : α → ℝ) (v : β → ℝ)
    (hp : IsProbability p) (hu : IsProbability u) (hv : IsProbability v)
    (hsu : SupportedBy (firstMarginal p) u) (hsv : SupportedBy (secondMarginal p) v) :
    relativeEntropy (firstMarginal p) u + relativeEntropy (secondMarginal p) v ≤
      relativeEntropy p (product u v) := by
  rw [relativeEntropy_product_reference p u v hp hu hv hsu hsv]
  have hn := relativeEntropy_nonneg p (product (firstMarginal p) (secondMarginal p)) hp
    (product_isProbability _ _ (firstMarginal_isProbability p hp)
      (secondMarginal_isProbability p hp)) (joint_supportedBy_product_marginals p hp)
  linarith

end IndependentSetsGames.Foundations.Information

end OAI
