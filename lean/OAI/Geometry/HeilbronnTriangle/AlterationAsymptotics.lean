import Mathlib

namespace OAI


noncomputable section

open Filter
open scoped Topology

namespace Problem355

theorem tendsto_log_sq_div_pow_nine :
    Tendsto (fun r : ℝ => (Real.log r) ^ 2 / r ^ 9) atTop (𝓝 0) := by
  simpa only [Real.rpow_ofNat] using
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (show 0 < (9 : ℝ) by norm_num)).tendsto_div_nhds_zero

theorem log_two_mul_le_of_polynomial_bound
    {r N A : ℝ} (hr : 2 ≤ r) (hN : 1 ≤ N)
    (hbound : N ≤ Real.rpow r A) :
    Real.log (2 * N) ≤ (A + 1) * Real.log r := by
  have hr0 : 0 < r := by linarith
  have hN0 : 0 < N := by linarith
  calc
    Real.log (2 * N) ≤ Real.log (r * Real.rpow r A) := by
      apply Real.log_le_log (by positivity)
      exact mul_le_mul hr hbound hN0.le hr0.le
    _ = (A + 1) * Real.log r := by
      simp only [Real.rpow_eq_pow]
      rw [Real.log_mul hr0.ne' (Real.rpow_pos_of_pos hr0 A).ne']
      simp only [Real.log_rpow hr0]
      ring

theorem tendsto_box_log_sq_div_pow_nine
    {α : Type*} {l : Filter α} {r N : α → ℝ} {A : ℝ}
    (hr : Tendsto r l atTop)
    (hbound : ∀ᶠ i in l, 1 ≤ N i ∧ N i ≤ Real.rpow (r i) A) :
    Tendsto (fun i => (Real.log (2 * N i)) ^ 2 / (r i) ^ 9) l (𝓝 0) := by
  have hmajor : Tendsto (fun i => (A + 1) ^ 2 *
      ((Real.log (r i)) ^ 2 / (r i) ^ 9)) l (𝓝 0) := by
    simpa using (tendsto_log_sq_div_pow_nine.comp hr).const_mul ((A + 1) ^ 2)
  apply squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [hr.eventually_ge_atTop 2] with i hi
    positivity
  · filter_upwards [hr.eventually_ge_atTop 2, hbound] with i hi hNi
    have hlog0 : 0 ≤ Real.log (2 * N i) := Real.log_nonneg (by linarith [hNi.1])
    have hlog := log_two_mul_le_of_polynomial_bound hi hNi.1 hNi.2
    have hsq : (Real.log (2 * N i)) ^ 2 ≤
        ((A + 1) * Real.log (r i)) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hlog)
        (add_nonneg hlog0 (hlog0.trans hlog))]
    calc
      (Real.log (2 * N i)) ^ 2 / (r i) ^ 9 ≤
          ((A + 1) * Real.log (r i)) ^ 2 / (r i) ^ 9 :=
        div_le_div_of_nonneg_right hsq (by positivity)
      _ = (A + 1) ^ 2 * ((Real.log (r i)) ^ 2 / (r i) ^ 9) := by ring

theorem sample_half_le_nat_floor {a : ℝ} (ha : 2 ≤ a) :
    a / 2 ≤ (⌊a⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one a
  linarith

theorem floor_sample_properties {α : Type*} {l : Filter α} {a : α → ℝ}
    (ha : Tendsto a l atTop) :
    Tendsto (fun i => ⌊a i⌋₊) l atTop ∧
      (∀ᶠ i in l, 3 ≤ ⌊a i⌋₊ ∧ a i / 2 ≤ (⌊a i⌋₊ : ℝ)) := by
  have hf : Tendsto (fun i => ⌊a i⌋₊) l atTop := tendsto_nat_floor_atTop.comp ha
  refine ⟨hf, ?_⟩
  filter_upwards [hf.eventually_ge_atTop 3, ha.eventually_ge_atTop 2] with i hi hi'
  exact ⟨hi, sample_half_le_nat_floor hi'⟩

theorem tendsto_real_sample_atTop
    {α : Type*} {l : Filter α} {r N τ : α → ℝ}
    (hr : Tendsto r l atTop)
    (hscale : ∀ᶠ i in l, 0 < τ i ∧ τ i ≤ (N i) ^ 3) :
    Tendsto (fun i => r i * Real.sqrt ((N i) ^ 3 / τ i)) l atTop := by
  apply tendsto_atTop_mono' l ?_ hr
  filter_upwards [hr.eventually_ge_atTop 0, hscale] with i hri hi
  have hratio : (1 : ℝ) ≤ (N i) ^ 3 / τ i :=
    (le_div_iff₀ hi.1).2 (by simpa using hi.2)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt ((N i) ^ 3 / τ i) := by
    simpa using Real.sqrt_le_sqrt hratio
  simpa using mul_le_mul_of_nonneg_left hsqrt hri

theorem sample_floor_le_polynomial
    {r H τ : ℝ} (hr : 0 ≤ r) (hH : 0 ≤ H) (hτ : 1 ≤ τ) :
    (⌊r * Real.sqrt ((H ^ 10) ^ 3 / τ)⌋₊ : ℝ) ≤ r * H ^ 15 := by
  have hdiv : (H ^ 10) ^ 3 / τ ≤ (H ^ 10) ^ 3 :=
    div_le_self (by positivity) hτ
  calc
    (⌊r * Real.sqrt ((H ^ 10) ^ 3 / τ)⌋₊ : ℝ) ≤
        r * Real.sqrt ((H ^ 10) ^ 3 / τ) := Nat.floor_le (by positivity)
    _ ≤ r * Real.sqrt ((H ^ 10) ^ 3) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdiv) hr
    _ = r * H ^ 15 := by
      rw [show (H ^ 10) ^ 3 = (H ^ 15) ^ 2 by ring, Real.sqrt_sq (by positivity)]

theorem pair_error_le_inverse_pow
    {n r H : ℝ} (hr : 0 < r) (hH : r ≤ H)
    (hn : n ≤ r * H ^ 15) :
    n * H ^ 6 / (H ^ 10) ^ 3 ≤ 1 / r ^ 8 := by
  have hH0 : 0 < H := hr.trans_le hH
  calc
    n * H ^ 6 / (H ^ 10) ^ 3 ≤
        (r * H ^ 15) * H ^ 6 / (H ^ 10) ^ 3 := by gcongr
    _ = r / H ^ 9 := by field_simp
    _ ≤ r / r ^ 9 := by gcongr
    _ = 1 / r ^ 8 := by field_simp

theorem sample_floor_square_bound
    {r N τ : ℝ} (hr : 0 ≤ r) (hN : 0 ≤ N) (hτ : 0 < τ) :
    (⌊r * Real.sqrt (N ^ 3 / τ)⌋₊ : ℝ) ^ 2 * τ ≤ r ^ 2 * N ^ 3 := by
  have ha : 0 ≤ r * Real.sqrt (N ^ 3 / τ) := by positivity
  have hf := Nat.floor_le ha
  have hf0 : 0 ≤ (⌊r * Real.sqrt (N ^ 3 / τ)⌋₊ : ℝ) := Nat.cast_nonneg _
  have hsq : (⌊r * Real.sqrt (N ^ 3 / τ)⌋₊ : ℝ) ^ 2 ≤
      (r * Real.sqrt (N ^ 3 / τ)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hf) (add_nonneg ha hf0)]
  calc
    (⌊r * Real.sqrt (N ^ 3 / τ)⌋₊ : ℝ) ^ 2 * τ ≤
        (r * Real.sqrt (N ^ 3 / τ)) ^ 2 * τ :=
      mul_le_mul_of_nonneg_right hsq hτ.le
    _ = r ^ 2 * N ^ 3 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ N ^ 3 / τ)]
      field_simp

theorem triple_error_le_log_majorant
    {n r N τ h C L : ℝ} (hr : 0 < r) (hN : 0 < N) (hτ : 0 < τ)
    (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsample : n ^ 2 * τ ≤ r ^ 2 * N ^ 3)
    (hmodulus : h ≤ C * τ * r ^ 30) :
    n ^ 2 * L * h / (N ^ 3 * r ^ 41) ≤ C * L / r ^ 9 := by
  have hnratio : n ^ 2 * τ / N ^ 3 ≤ r ^ 2 :=
    (div_le_iff₀ (pow_pos hN 3)).2 hsample
  have hhratio : h / τ ≤ C * r ^ 30 :=
    (div_le_iff₀ hτ).2 (by nlinarith [hmodulus])
  calc
    n ^ 2 * L * h / (N ^ 3 * r ^ 41) =
        (n ^ 2 * τ / N ^ 3) * (h / τ) * L / r ^ 41 := by
      field_simp
    _ ≤ r ^ 2 * (C * r ^ 30) * L / r ^ 41 := by gcongr
    _ = C * L / r ^ 9 := by field_simp

theorem tendsto_alteration_error_majorant
    {α : Type*} {l : Filter α} {r N : α → ℝ} {A : ℝ}
    (hr : Tendsto r l atTop)
    (hbound : ∀ᶠ i in l, 1 ≤ N i ∧ N i ≤ Real.rpow (r i) A)
    (Cpair Ctriple : ℝ) :
    Tendsto (fun i => Cpair / (r i) ^ 8 +
      Ctriple * ((Real.log (2 * N i)) ^ 2 / (r i) ^ 9)) l (𝓝 0) := by
  have hpair : Tendsto (fun i => Cpair / (r i) ^ 8) l (𝓝 0) := by
    simpa [div_eq_mul_inv, inv_pow] using
      ((tendsto_inv_atTop_zero.comp hr).pow 8).const_mul Cpair
  simpa using hpair.add
    ((tendsto_box_log_sq_div_pow_nine hr hbound).const_mul Ctriple)

theorem alteration_error_eventually_lt_one
    {α : Type*} {l : Filter α} {r N Z : α → ℝ} {A Cpair Ctriple : ℝ}
    (hr : Tendsto r l atTop)
    (hbound : ∀ᶠ i in l, 1 ≤ N i ∧ N i ≤ Real.rpow (r i) A)
    (hZ : ∀ᶠ i in l, Z i ≤ Cpair / (r i) ^ 8 +
      Ctriple * ((Real.log (2 * N i)) ^ 2 / (r i) ^ 9)) :
    ∀ᶠ i in l, Z i < 1 := by
  have hsmall := (tendsto_alteration_error_majorant hr hbound Cpair Ctriple).eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hZ, hsmall] with i hi hi'
  exact hi.trans_lt hi'

end Problem355

end

end OAI
