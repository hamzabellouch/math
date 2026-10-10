import Mathlib

namespace OAI

noncomputable section
namespace AngularSampling

lemma secant_left (l r : ℝ) :
    (1 + l * r) / 4 - l * ((l + r) / 4) = (1 - l ^ 2) / 4 := by ring

lemma secant_right (l r : ℝ) :
    (1 + l * r) / 4 - r * ((l + r) / 4) = (1 - r ^ 2) / 4 := by ring

lemma sampled_compatibility (p q : ℝ) :
    (1 + q ^ 2) / 4 - (1 + p ^ 2) / 4 =
      ((p + q) / 2) * (q / 2 - p / 2) := by ring

lemma sampled_outer_left : (1 + (-1 : ℝ) ^ 2) / 4 - (-1) * ((-1) / 2) = 0 := by norm_num
lemma sampled_outer_right : (1 + (1 : ℝ) ^ 2) / 4 - 1 * (1 / 2) = 0 := by norm_num

lemma cubic_secant_left (l r : ℝ) :
    (1 + l * r) / 2 - l * ((l + r) / 2) = (1 - l ^ 2) / 2 := by ring

lemma cubic_secant_right (l r : ℝ) :
    (1 + l * r) / 2 - r * ((l + r) / 2) = (1 - r ^ 2) / 2 := by ring

lemma cubic_balance (ε a c r q x y S T : ℝ)
    (hy : y = r * S + ε * a * x) (hx : x = q * T - ε * c * y) :
    q * y - r * x = r * q * (S - T) + ε * (q * a * x + r * c * y) := by
  nlinarith [congrArg (fun z : ℝ => q * z) hy,
    congrArg (fun z : ℝ => r * z) hx]

lemma cubic_coarse_bound {ε P : ℝ} (he : 0 ≤ ε) (he' : ε ≤ 1 / 2)
    (hP : 0 ≤ P) (h : P ≤ ε * P + 4 * ε ^ 2 + 4 * ε ^ 3) :
    P ≤ 12 * ε ^ 2 := by
  have h1 := mul_nonneg (sub_nonneg.mpr he') hP
  have h2 := mul_nonneg (sub_nonneg.mpr he') (pow_nonneg he 2)
  nlinarith

lemma cubic_error_bound {ε P Δ : ℝ} (he : 0 ≤ ε) (he' : ε ≤ 1 / 2)
    (hP : P ≤ 12 * ε ^ 2) (hΔ : Δ ≤ ε ^ 2) :
    ε * P + 2 * ε ^ 2 * P + 4 * ε ^ 3 + 4 * ε * Δ ≤ 32 * ε ^ 3 := by
  have h1 := mul_le_mul_of_nonneg_left hP he
  have h2 := mul_le_mul_of_nonneg_left hP (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg ε))
  have h3 := mul_le_mul_of_nonneg_left hΔ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) he)
  have h4 := mul_nonneg (sub_nonneg.mpr he') (pow_nonneg he 3)
  nlinarith

lemma cubic_coefficient_bound {a c r q Δ D E : ℝ}
    (ha : a ≤ (1 + r ^ 2) / 2 + Δ) (hc : c ≤ (1 + q ^ 2) / 2 + Δ)
    (hΔ : 0 ≤ Δ) (hr : r ^ 2 ≤ 1) (hq : q ^ 2 ≤ 1)
    (hD : (r ^ 2 + r ^ 4) / 2 ≤ D) (hE : (q ^ 2 + q ^ 4) / 2 ≤ E) :
    a * q ^ 2 + c * r ^ 2 ≤ D + E + 2 * Δ := by
  have h1 := mul_le_mul_of_nonneg_right ha (sq_nonneg q)
  have h2 := mul_le_mul_of_nonneg_right hc (sq_nonneg r)
  have h3 := mul_nonneg hΔ (sub_nonneg.mpr hq)
  have h4 := mul_nonneg hΔ (sub_nonneg.mpr hr)
  nlinarith [sq_nonneg (q ^ 2 - r ^ 2)]

lemma cubic_final_bound {ε Δ P D E A : ℝ}
    (he : 0 ≤ ε) (he' : ε ≤ 1 / 2) (hΔ : Δ ≤ ε ^ 2)
    (hA : A ≤ D + E + 2 * Δ)
    (hP : P ≤ ε ^ 2 * A + 32 * ε ^ 3) :
    P ≤ ε ^ 2 * (D + E) + 33 * ε ^ 3 := by
  have h1 := mul_le_mul_of_nonneg_left hA (sq_nonneg ε)
  have h2 := mul_le_mul_of_nonneg_left hΔ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg ε))
  have h3 := mul_nonneg (sub_nonneg.mpr he') (pow_nonneg he 3)
  nlinarith

lemma abs_product_three_le_two {u v w : ℝ}
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) (hw : |w| ≤ 2) :
    |u * v * w| ≤ 2 := by
  rw [abs_mul, abs_mul]
  have huv : |u| * |v| ≤ 1 := by
    calc
      |u| * |v| ≤ 1 * 1 := mul_le_mul hu hv (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  calc
    |u| * |v| * |w| ≤ 1 * 2 := mul_le_mul huv hw (abs_nonneg _) (by norm_num)
    _ = 2 := by ring

lemma abs_product_four_le_two {u v w z : ℝ}
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) (hw : |w| ≤ 1) (hz : |z| ≤ 2) :
    |u * v * w * z| ≤ 2 := by
  have huv : |u * v| ≤ 1 := by
    rw [abs_mul]
    calc
      |u| * |v| ≤ 1 * 1 := mul_le_mul hu hv (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  exact abs_product_three_le_two huv hw hz

lemma cubic_sampling_error {b d r q x y Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hb : |b - r| ≤ Δ) (hd : |d - q| ≤ Δ)
    (hx : |x| ≤ 2) (hy : |y| ≤ 2) :
    |(d - q) * y - (b - r) * x| ≤ 4 * Δ := by
  calc
    |(d - q) * y - (b - r) * x| ≤ |(d - q) * y| + |(b - r) * x| := abs_sub _ _
    _ = |d - q| * |y| + |b - r| * |x| := by rw [abs_mul, abs_mul]
    _ ≤ Δ * 2 + Δ * 2 := add_le_add
      (mul_le_mul hd hy (abs_nonneg _) hΔ)
      (mul_le_mul hb hx (abs_nonneg _) hΔ)
    _ = 4 * Δ := by ring

lemma cubic_difference_bound {q r S T P : ℝ}
    (hq : |q| ≤ 1) (hr : |r| ≤ 1) (hS : 1 ≤ S) (hT : 1 ≤ T)
    (hP : P = S + T - 2) :
    r * q * (S - T) ≤ P := by
  have hST : |S - T| ≤ P := by rw [abs_le]; constructor <;> linarith
  have hqr : |r * q| ≤ 1 := by
    rw [abs_mul]
    calc
      |r| * |q| ≤ 1 * 1 := mul_le_mul hr hq (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  calc
    r * q * (S - T) ≤ |r * q * (S - T)| := le_abs_self _
    _ = |r * q| * |S - T| := abs_mul _ _
    _ ≤ 1 * P := mul_le_mul hqr hST (abs_nonneg _) (by norm_num)
    _ = P := one_mul _

lemma cubic_initial_estimate {ε a b c d r q x y S T P Δ : ℝ}
    (he : 0 ≤ ε) (hΔ : 0 ≤ Δ)
    (hb : |b - r| ≤ Δ) (hd : |d - q| ≤ Δ)
    (hq : |q| ≤ 1) (hr : |r| ≤ 1) (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hS : 1 ≤ S) (hT : 1 ≤ T) (hP : P = S + T - 2)
    (hbalance : P = ε * (d * y - b * x))
    (hy' : y = r * S + ε * a * x) (hx' : x = q * T - ε * c * y) :
    P ≤ ε * P + ε ^ 2 * (q * a * x + r * c * y) + 4 * ε * Δ := by
  have herr := cubic_sampling_error hΔ hb hd hx hy
  have hdiff := cubic_difference_bound hq hr hS hT hP
  have heq := cubic_balance ε a c r q x y S T hy' hx'
  have herr' : (d - q) * y - (b - r) * x ≤ 4 * Δ :=
    (le_abs_self _).trans herr
  have h1 := mul_le_mul_of_nonneg_left herr' he
  have h2 := mul_le_mul_of_nonneg_left hdiff he
  have heqε := congrArg (fun z : ℝ => ε * z) heq
  nlinarith only [hbalance, heqε, h1, h2]

lemma cubic_refined_term {ε a c q x y T P : ℝ}
    (he : 0 ≤ ε) (ha : 0 ≤ a) (ha' : a ≤ 1) (hc : 0 ≤ c) (hc' : c ≤ 1)
    (hq : |q| ≤ 1) (hy : |y| ≤ 2) (hT : 1 ≤ T) (hTP : T - 1 ≤ P)
    (hx : x = q * T - ε * c * y) :
    q * a * x ≤ a * q ^ 2 + P + 2 * ε := by
  have hq2 : q ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one q).mpr hq
  have hk0 : 0 ≤ a * q ^ 2 := mul_nonneg ha (sq_nonneg _)
  have hk1 : a * q ^ 2 ≤ 1 := by
    calc
      a * q ^ 2 ≤ 1 * 1 := mul_le_mul ha' hq2 (sq_nonneg _) (by norm_num)
      _ = 1 := by ring
  have h1 : a * q ^ 2 * (T - 1) ≤ P := by
    calc
      a * q ^ 2 * (T - 1) ≤ 1 * P :=
        mul_le_mul hk1 hTP (by linarith) (by norm_num)
      _ = P := by ring
  have hprod := abs_product_four_le_two hq
    (by rwa [abs_of_nonneg ha]) (by rwa [abs_of_nonneg hc]) hy
  have h2 : -(q * a * c * y) ≤ 2 := (neg_le_abs _).trans hprod
  have h3 := mul_le_mul_of_nonneg_left h2 he
  have heq : q * a * x = a * q ^ 2 + a * q ^ 2 * (T - 1) - ε * (q * a * c * y) := by
    rw [hx]; ring
  linarith only [h1, h3, heq]

theorem noradial_failure {ε Δ a b c d r q x y S T D E : ℝ}
    (he : 0 < ε) (he' : ε ≤ 1 / 2) (hΔ : 0 ≤ Δ) (hΔ' : Δ ≤ ε ^ 2)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hc : 0 ≤ c) (hc' : c ≤ 1)
    (hb : |b - r| ≤ Δ) (hd : |d - q| ≤ Δ)
    (hr : |r| ≤ 1) (hq : |q| ≤ 1) (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hy' : y = r * S + ε * a * x) (hx' : x = q * T - ε * c * y)
    (hST : S + T = 2 + ε * (d * y - b * x))
    (haR : a ≤ (1 + r ^ 2) / 2 + Δ) (hcQ : c ≤ (1 + q ^ 2) / 2 + Δ)
    (hD : (r ^ 2 + r ^ 4) / 2 ≤ D) (hE : (q ^ 2 + q ^ 4) / 2 ≤ E) :
    S ≤ 1 + ε ^ 2 * D + 100 * ε ^ 3 ∨ T ≤ 1 + ε ^ 2 * E + 100 * ε ^ 3 := by
  by_contra h
  push Not at h
  obtain ⟨hS, hT⟩ := h
  have he0 := he.le
  have he2 := sq_nonneg ε
  have he3 : 0 < ε ^ 3 := pow_pos he 3
  have hD0 : 0 ≤ D := by nlinarith [sq_nonneg r, sq_nonneg (r ^ 2)]
  have hE0 : 0 ≤ E := by nlinarith [sq_nonneg q, sq_nonneg (q ^ 2)]
  have hS1 : 1 ≤ S := by nlinarith [mul_nonneg he2 hD0]
  have hT1 : 1 ≤ T := by nlinarith [mul_nonneg he2 hE0]
  let P := S + T - 2
  have hPdef : P = S + T - 2 := rfl
  have hP0 : 0 ≤ P := by dsimp [P]; linarith
  have hPbal : P = ε * (d * y - b * x) := by dsimp [P]; linarith
  have hinit := cubic_initial_estimate he0 hΔ hb hd hq hr hx hy hS1 hT1 hPdef hPbal hy' hx'
  have habs : |a| ≤ 1 := by rwa [abs_of_nonneg ha]
  have hcabs : |c| ≤ 1 := by rwa [abs_of_nonneg hc]
  have hA : q * a * x + r * c * y ≤ 4 := by
    have h1 := (le_abs_self _).trans (abs_product_three_le_two hq habs hx)
    have h2 := (le_abs_self _).trans (abs_product_three_le_two hr hcabs hy)
    linarith
  have hcoarse : P ≤ 12 * ε ^ 2 := by
    apply cubic_coarse_bound he0 he' hP0
    have h1 := mul_le_mul_of_nonneg_left hA he2
    have h2 := mul_le_mul_of_nonneg_left hΔ' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) he0)
    nlinarith only [hinit, h1, h2]
  have hTP : T - 1 ≤ P := by dsimp [P]; linarith
  have hSP : S - 1 ≤ P := by dsimp [P]; linarith
  have hterm1 := cubic_refined_term he0 ha ha' hc hc' hq hy hT1 hTP hx'
  have hyneg : y = r * S - ε * a * (-x) := by nlinarith only [hy']
  have hterm2 := cubic_refined_term he0 hc hc' ha ha' hr
    (show |(-x)| ≤ 2 by simpa using hx) hS1 hSP hyneg
  have hterms : q * a * x + r * c * y ≤ a * q ^ 2 + c * r ^ 2 + 2 * P + 4 * ε := by
    linarith only [hterm1, hterm2]
  have herr := cubic_error_bound he0 he' hcoarse hΔ'
  have hrefined : P ≤ ε ^ 2 * (a * q ^ 2 + c * r ^ 2) + 32 * ε ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hterms he2
    nlinarith only [hinit, hmul, herr]
  have hcoeff := cubic_coefficient_bound haR hcQ hΔ
    ((sq_le_one_iff_abs_le_one r).mpr hr) ((sq_le_one_iff_abs_le_one q).mpr hq) hD hE
  have hfinal := cubic_final_bound he0 he' hΔ' hcoeff hrefined
  dsimp [P] at hfinal
  nlinarith only [hS, hT, hfinal, he3]

end AngularSampling

end

end OAI
