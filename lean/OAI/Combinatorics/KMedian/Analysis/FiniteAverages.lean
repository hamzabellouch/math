import Mathlib
import OAI.Combinatorics.KMedian.Analysis.Coefficients

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

noncomputable def psi (p q : ℝ) : ℝ := (1 - q) / (1 - p * q)

noncomputable def kZero (p : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - p)) / (1 + Real.sqrt (1 - p))

noncomputable def kappa (p s q : ℝ) : ℝ :=
  (1 - p * s) * psi p q - (1 - q)

theorem denominator_pos {p q : ℝ} (hp : p ≤ 1 / 2)
    (hp0 : 0 ≤ p) (hq : q ≤ 1) : 0 < 1 - p * q := by
  nlinarith [mul_le_mul_of_nonneg_left hq hp0]

theorem psi_nonneg {p q : ℝ} (hp : p ≤ 1 / 2)
    (hp0 : 0 ≤ p) (hq : q ≤ 1) : 0 ≤ psi p q := by
  exact div_nonneg (sub_nonneg.mpr hq) (denominator_pos hp hp0 hq).le

theorem psi_le_one {p q : ℝ} (hp : p ≤ 1 / 2) (hp0 : 0 ≤ p)
    (hq0 : 0 ≤ q) (hq : q ≤ 1) : psi p q ≤ 1 := by
  rw [psi, div_le_one (denominator_pos hp hp0 hq)]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - p) hq0]

theorem psi_affine_majorant {p q : ℝ} (hp : p ≤ 1 / 2) (hp0 : 0 ≤ p)
    (hq0 : 0 ≤ q) (hq : q ≤ 1) : psi p q ≤ 1 - q + p * q := by
  have h₁ := psi_le_one hp hp0 hq0 hq
  have hid : psi p q = 1 - q + p * q * psi p q := by
    have he : psi p q * (1 - p * q) = 1 - q :=
      div_mul_cancel₀ _ (ne_of_gt (denominator_pos hp hp0 hq))
    nlinarith only [he]
  have h₂ := mul_le_mul_of_nonneg_left h₁ (mul_nonneg hp0 hq0)
  rw [mul_one] at h₂
  linarith

theorem kZero_nonneg {p : ℝ} (hp0 : 0 ≤ p) :
    0 ≤ kZero p := by
  have hs : Real.sqrt (1 - p) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    linarith
  exact div_nonneg (sub_nonneg.mpr hs) (by positivity)

theorem kappa_zero_le {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hq : q ≤ 1) : kappa p 0 q ≤ kZero p := by
  have hd := denominator_pos hp hp0 hq
  have hs0 : 0 ≤ Real.sqrt (1 - p) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (1 - p) ^ 2 = 1 - p := Real.sq_sqrt (by linarith)
  have hp_eq : p = 1 - Real.sqrt (1 - p) ^ 2 := by linarith
  have hk0 := kZero_nonneg hp0
  have identity : kZero p * (1 - p * q) - p * q * (1 - q) =
      kZero p * ((1 + Real.sqrt (1 - p)) * q - 1) ^ 2 := by
    unfold kZero
    field_simp [ne_of_gt (show 0 < 1 + Real.sqrt (1 - p) by positivity)]
    nlinarith [sq_nonneg (Real.sqrt (1 - p) * q)]
  have hid : kappa p 0 q = p * q * (1 - q) / (1 - p * q) := by
    apply (eq_div_iff (ne_of_gt hd)).mpr
    unfold kappa
    simp only [mul_zero, sub_zero, one_mul]
    have he : psi p q * (1 - p * q) = 1 - q :=
      div_mul_cancel₀ _ (ne_of_gt hd)
    nlinarith only [he]
  rw [hid, div_le_iff₀ hd]
  have h := mul_nonneg hk0 (sq_nonneg ((1 + Real.sqrt (1 - p)) * q - 1))
  linarith [identity]

theorem kappa_one_le {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hq : q ≤ 1) : kappa p 1 q ≤ 0 := by
  have hd := denominator_pos hp hp0 hq
  have hid : kappa p 1 q = -p * (1 - q) ^ 2 / (1 - p * q) := by
    unfold kappa psi
    simp only [mul_one]
    field_simp [ne_of_gt hd]
    ring
  rw [hid]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp0) (sq_nonneg _)) hd.le

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

noncomputable def average {I : Type*} [Fintype I] (π f : I → ℝ) : ℝ :=
  ∑ i, π i * f i

theorem average_mono {I : Type*} [Fintype I] {π f h : I → ℝ}
    (hπ : ∀ i, 0 ≤ π i) (hfh : ∀ i, f i ≤ h i) : average π f ≤ average π h := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hfh i) (hπ i))

theorem average_nonneg {I : Type*} [Fintype I] {π f : I → ℝ}
    (hπ : ∀ i, 0 ≤ π i) (hf : ∀ i, 0 ≤ f i) : 0 ≤ average π f := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hπ i) (hf i))

theorem average_const {I : Type*} [Fintype I] {π : I → ℝ}
    (hπ : ∑ i, π i = 1) (c : ℝ) : average π (fun _ => c) = c := by
  simp only [average, ← Finset.sum_mul, hπ, one_mul]

theorem average_add {I : Type*} [Fintype I] (π f h : I → ℝ) :
    average π (fun i => f i + h i) = average π f + average π h := by
  simp only [average, mul_add, Finset.sum_add_distrib]

theorem average_sub {I : Type*} [Fintype I] (π f h : I → ℝ) :
    average π (fun i => f i - h i) = average π f - average π h := by
  simp only [average, mul_sub, Finset.sum_sub_distrib]

theorem average_mul {I : Type*} [Fintype I] (π f : I → ℝ) (c : ℝ) :
    average π (fun i => c * f i) = c * average π f := by
  simp only [average, ← Finset.mul_sum, mul_left_comm]

theorem average_mul_right {I : Type*} [Fintype I] (π f : I → ℝ) (c : ℝ) :
    average π (fun i => f i * c) = average π f * c := by
  simp only [average, Finset.sum_mul, mul_assoc]

noncomputable def C (p : ℝ) (s : Bool) : ℝ := if s then 1 - p else 1
noncomputable def k (p : ℝ) (s : Bool) : ℝ := if s then 0 else kZero p
noncomputable def H (h : ℝ) (s : Bool) : ℝ := if s then 1 / 4 else h
noncomputable def d (s : Bool) : ℝ := if s then 2 / 5 else 13 / 25

noncomputable def K (p z : ℝ) (b : Bool → ℝ) (s : Bool) (r : ℝ) : ℝ :=
  C p s - k p s - b s * r + (8 / 5) * z
noncomputable def L (p m z : ℝ) (b : Bool → ℝ) (s : Bool) (r : ℝ) : ℝ :=
  (C p s - m - b s) * r + (2 / 5) * z
noncomputable def M (p a : ℝ) (s : Bool) (r : ℝ) : ℝ :=
  (1 - r) * a + C p s * p * r
noncomputable def G (p m a z : ℝ) (b : Bool → ℝ) (s : Bool) (r : ℝ) : ℝ :=
  M p a s r - L p m z b s r

noncomputable def centered (p m a z : ℝ) (b : Bool → ℝ)
    (s : Bool) (D q Z : ℝ) : ℝ :=
  (m * D + b s * (D + 1)) * q +
    D * (C p s * psi p q + a * (1 - q) - C p s) -
    ((2 / 5) * D + 8 / 5) * z - C p s + k p s -
    (k p s - (C p s * psi p q - (1 - q))) * Z

theorem C_pos {p : ℝ} (hp : p ≤ 1 / 2) (s : Bool) : 0 < C p s := by
  cases s <;> simp only [C, Bool.false_eq_true, ↓reduceIte] <;> linarith

theorem C_le_one {p : ℝ} (hp : 0 ≤ p) (s : Bool) : C p s ≤ 1 := by
  cases s <;> simp only [C, Bool.false_eq_true, ↓reduceIte] <;> linarith

theorem centering_gap_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hq : q ≤ 1) (s : Bool) : 0 ≤ k p s - (C p s * psi p q - (1 - q)) := by
  cases s
  · have he := kappa_zero_le hp0 hp hq
    simpa only [kappa, mul_zero, sub_zero, one_mul, k, C, Bool.false_eq_true,
      ↓reduceIte] using sub_nonneg.mpr he
  · have he := kappa_one_le hp0 hp hq
    simpa only [kappa, mul_one, k, C, ↓reduceIte] using sub_nonneg.mpr he

structure ScalarBounds (p m a z h : ℝ) (b : Bool → ℝ) : Prop where
  p_nonneg : 0 ≤ p
  p_le_half : p ≤ 1 / 2
  m_nonneg : 0 ≤ m
  z_nonneg : 0 ≤ z
  h_nonneg : 0 ≤ h
  h_le : h ≤ 197 / 500
  b_nonneg : ∀ s, 0 ≤ b s
  first : ∀ s r, 0 < r → r ≤ 1 →
    m + b s - (2 / 5) * z / r ≤ C p s * (1 - p) / (1 - p * r)
  linear : ∀ s r, 0 ≤ r → r ≤ 1 →
    0 ≤ L p m z b s r ∧ 0 < K p z b s r ∧
      d s * G p m a z b s r ≤ K p z b s r
  charge : ∀ s r, 0 ≤ r → r ≤ 1 →
    0 ≤ ((C p s * H h s - b s) * r + (8 / 5) * z) * M p a s r +
      (C p s - k p s - C p s * H h s * r) * L p m z b s r
  type_zero : ∀ s q, 0 ≤ q → q ≤ 1 →
    h ≤ C p s - k p s + (8 / 5) * z - b s * q +
      (13 / 25) * (k p s - (C p s * psi p q - (1 - q)))
  type_one : ∀ s, 1 / 4 ≤ C p s - k p s + (8 / 5) * z - b s

theorem centered_le_linear {p m a z : ℝ} {b : Bool → ℝ}
    {s : Bool} {D q Z : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hD : 0 ≤ D) (hq0 : 0 ≤ q) (hq : q ≤ 1) (hZ : 0 ≤ Z) :
    centered p m a z b s D q Z ≤ D * G p m a z b s q - K p z b s q := by
  have hψ := psi_affine_majorant hp hp0 hq0 hq
  have hgap := centering_gap_nonneg hp0 hp hq s
  have h₁ := mul_le_mul_of_nonneg_left hψ (mul_nonneg hD (C_pos hp s).le)
  have h₂ := mul_nonneg hgap hZ
  unfold centered G M L K
  nlinarith only [h₁, h₂]

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

theorem affine_hinge_nonpos {a b H c D χ : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D) (hDc : D ≤ c) (hH : 0 ≤ H) (hHc : H ≤ c)
    (hχ : 0 ≤ χ) (hzero : b + χ * H ≤ 0) (hcap : b + a * c ≤ 0) :
    b + a * D + χ * max (H - D) 0 ≤ 0 := by
  have hh : c * max (H - D) 0 ≤ (c - D) * H := by
    rcases le_total 0 (H - D) with h | h
    · rw [max_eq_left h]
      nlinarith [mul_nonneg hD (sub_nonneg.mpr hHc)]
    · rw [max_eq_right h, mul_zero]
      exact mul_nonneg (sub_nonneg.mpr hDc) hH
  have hhχ := mul_le_mul_of_nonneg_left hh hχ
  have h₀ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hDc) hzero
  have h₁ := mul_nonpos_of_nonneg_of_nonpos hD hcap
  have he : c * (b + a * D + χ * max (H - D) 0) ≤ 0 := by
    nlinarith only [hhχ, h₀, h₁]
  exact nonpos_of_mul_nonpos_right he hc

theorem average_exchange {I : Type*} [Fintype I] (π : I → ℝ) (Γ : I → I → ℝ) :
    average π (fun i => average π (Γ i)) =
      average π (fun i => average π (fun t => Γ t i)) := by
  unfold average
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext t
  ring

theorem charge_cancellation {I : Type*} [Fintype I] (π F : I → ℝ)
    (Γ : I → I → ℝ) (receives : I → Prop)
    (hπ : ∀ i, 0 ≤ π i) (hΓ : ∀ i t, 0 ≤ Γ i t)
    (hout : ∀ i, 0 < F i → F i ≤ average π (Γ i))
    (hin : ∀ i, receives i → F i + average π (fun t => Γ t i) ≤ 0)
    (hsupport : ∀ i t, ¬ receives t → Γ i t = 0) : average π F ≤ 0 := by
  have hpoint : ∀ i, F i ≤ average π (Γ i) - average π (fun t => Γ t i) := by
    intro i
    by_cases hi : receives i
    · have h₁ := hin i hi
      have h₂ := average_nonneg hπ (hΓ i)
      linarith
    · have hzero : average π (fun t => Γ t i) = 0 := by
        simp only [average, hsupport _ _ hi, mul_zero, Finset.sum_const_zero]
      rw [hzero, sub_zero]
      by_cases hF : 0 < F i
      · exact hout i hF
      · exact le_trans (le_of_not_gt hF) (average_nonneg hπ (hΓ i))
  calc
    average π F ≤ average π (fun i => average π (Γ i) -
      average π (fun t => Γ t i)) := average_mono hπ hpoint
    _ = 0 := by rw [average_sub, average_exchange, sub_self]

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

noncomputable def rowValue {I : Type*} [Fintype I] (π Z q : I → ℝ)
    (p m a z : ℝ) (b : Bool → ℝ) (s : Bool) (D R : ℝ) : ℝ :=
  C p s * (1 - average π q) * R +
    (m * D + b s * (D + 1)) * average π q - C p s * (D + 1) -
    average π (fun t => (1 - q t) * max (Z t - a * D) 0) -
    ((2 / 5) * D + 8 / 5) * z

theorem taper_weighted_comparison {p q R D Z : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hq : q ≤ 1)
    (hcomp : q < 1 → R * (1 - p * q) ≤ D + Z) :
    (1 - q) * R ≤ psi p q * (D + Z) := by
  by_cases hq1 : q < 1
  · have he := mul_le_mul_of_nonneg_left (hcomp hq1) (sub_nonneg.mpr hq)
    unfold psi
    rw [div_mul_eq_mul_div, le_div_iff₀ (denominator_pos hp hp0 hq)]
    nlinarith only [he]
  · have : q = 1 := le_antisymm hq (le_of_not_gt hq1)
    simp only [this, sub_self, zero_mul, psi, zero_div]
    exact le_rfl

theorem row_as_average {I : Type*} [Fintype I] {π : I → ℝ}
    (hπ : ∑ i, π i = 1) (Z q : I → ℝ)
    (p m a z : ℝ) (b : Bool → ℝ) (s : Bool) (D R : ℝ) :
    rowValue π Z q p m a z b s D R = average π (fun t =>
      C p s * ((1 - q t) * R) + (m * D + b s * (D + 1)) * q t -
      C p s * (D + 1) - (1 - q t) * max (Z t - a * D) 0 -
      ((2 / 5) * D + 8 / 5) * z) := by
  simp only [rowValue, average_add, average_sub, average_mul, average_mul_right,
    average_const hπ]
  ring

theorem row_le_centered {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m a z : ℝ} {b : Bool → ℝ} {s : Bool} {D R : ℝ}
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1) (hZ : average π Z = 1)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hq : ∀ t, q t ≤ 1)
    (hcomp : ∀ t, q t < 1 → R * (1 - p * q t) ≤ D + Z t) :
    rowValue π Z q p m a z b s D R ≤
      average π (fun t => centered p m a z b s D (q t) (Z t)) := by
  have hpoint : ∀ t,
      C p s * ((1 - q t) * R) + (m * D + b s * (D + 1)) * q t -
      C p s * (D + 1) - (1 - q t) * max (Z t - a * D) 0 -
      ((2 / 5) * D + 8 / 5) * z ≤
        centered p m a z b s D (q t) (Z t) + k p s * (Z t - 1) := by
    intro t
    have h₁ := mul_le_mul_of_nonneg_left
      (taper_weighted_comparison hp0 hp (hq t) (hcomp t)) (C_pos hp s).le
    have h₂ := mul_le_mul_of_nonneg_left (le_max_left (Z t - a * D) (0 : ℝ))
      (sub_nonneg.mpr (hq t))
    unfold centered
    nlinarith only [h₁, h₂]
  rw [row_as_average hπ]
  refine (average_mono hπ0 hpoint).trans_eq ?_
  rw [average_add, average_mul, average_sub, average_const hπ, hZ]
  ring

theorem average_linear {I : Type*} [Fintype I] {π : I → ℝ}
    (hπ : ∑ t, π t = 1) (q : I → ℝ)
    (p m a z : ℝ) (b : Bool → ℝ) (s : Bool) (D : ℝ) :
    average π (fun t => D * G p m a z b s (q t) - K p z b s (q t)) =
      D * G p m a z b s (average π q) - K p z b s (average π q) := by
  simp only [G, M, L, K, average_add, average_sub, average_mul, average_mul_right,
    average_const hπ]

theorem row_le_linear {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m a z : ℝ} {b : Bool → ℝ} {s : Bool} {D R : ℝ}
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1) (hZ : average π Z = 1)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hD : 0 ≤ D) (hZ0 : ∀ t, 0 ≤ Z t)
    (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1)
    (hcomp : ∀ t, q t < 1 → R * (1 - p * q t) ≤ D + Z t) :
    rowValue π Z q p m a z b s D R ≤
      D * G p m a z b s (average π q) - K p z b s (average π q) := by
  refine (row_le_centered hπ0 hπ hZ hp0 hp hq hcomp).trans ?_
  rw [← average_linear hπ]
  exact average_mono hπ0 (fun t => centered_le_linear hp0 hp hD (hq0 t) (hq t) (hZ0 t))

theorem rate_comparison {I : Type*} [Fintype I] {π Z q : I → ℝ} {p D R : ℝ}
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1) (hZ : average π Z = 1)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hD : 0 ≤ D) (hZ0 : ∀ t, 0 ≤ Z t)
    (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1)
    (hcomp : ∀ t, q t < 1 → R * (1 - p * q t) ≤ D + Z t) :
    (1 - average π q) * R ≤ D + 1 := by
  have hpoint : ∀ t, (1 - q t) * R ≤ D + Z t := by
    intro t
    refine (taper_weighted_comparison hp0 hp (hq t) (hcomp t)).trans ?_
    have h := mul_le_mul_of_nonneg_right (psi_le_one hp hp0 (hq0 t) (hq t))
      (add_nonneg hD (hZ0 t))
    simpa only [one_mul] using h
  have he := average_mono hπ0 hpoint
  simpa only [average_add, average_sub, average_mul_right, average_const hπ, hZ] using he

theorem average_unit_bounds {I : Type*} [Fintype I] {π q : I → ℝ}
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1)
    (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1) :
    0 ≤ average π q ∧ average π q ≤ 1 := by
  refine ⟨average_nonneg hπ0 hq0, ?_⟩
  exact (average_mono hπ0 hq).trans_eq (average_const hπ 1)

end MetricKMedian.FiniteComparison


end
end

end OAI
