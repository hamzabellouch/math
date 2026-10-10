import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Determinants.NormalizedMasterBound

namespace OAI

namespace SiegelZeros

section
section
open Filter Topology

namespace WeightedTorusJets.FinalComparison

theorem not_eventually_master
    {ι : Type*} {l : Filter ι} [NeBot l]
    {r x e : ι → ℝ} {C A : ℝ}
    (hA : 0 < A) (hchoice : (C + 13 / 24) / A ≤ 1 / 16)
    (hr : ∀ᶠ n in l, r n ≤ 1 / 12)
    (hx : Tendsto x l (𝓝 A)) (he : Tendsto e l (𝓝 0)) :
    ¬ (∀ᶠ n in l,
      1 ≤ 3 / 4 * (1 + r n) + (C + 1 / 2 * (1 + r n)) / x n + e n) := by
  intro hmaster
  have hxpos : ∀ᶠ n in l, 0 < x n := hx.eventually (eventually_gt_nhds hA)
  have hlim : Tendsto
      (fun n ↦ 13 / 16 + (C + 13 / 24) / x n + e n) l
      (𝓝 (13 / 16 + (C + 13 / 24) / A)) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.div hx hA.ne')).add he
  have hle : 1 ≤ 13 / 16 + (C + 13 / 24) / A := ge_of_tendsto hlim (by
    filter_upwards [hr, hxpos, hmaster] with n hrn hxn hn
    have hfirst : 3 / 4 * (1 + r n) ≤ (13 : ℝ) / 16 := by linarith
    have hsecond : (C + 1 / 2 * (1 + r n)) / x n ≤ (C + 13 / 24) / x n :=
      (div_le_div_iff_of_pos_right hxn).mpr (by linarith)
    linarith)
  linarith

end WeightedTorusJets.FinalComparison

end

section
open Filter _root_.Real
open scoped Topology

namespace WeightedTorusJets

theorem tendsto_log_natCeil_rpow_div_log {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ ↦ log (⌈q ^ γ⌉₊ : ℝ) / log q) atTop (𝓝 γ) := by
  have hpow := tendsto_rpow_atTop hγ
  have hratio : Tendsto (fun q : ℝ ↦ (⌈q ^ γ⌉₊ : ℝ) / q ^ γ) atTop (𝓝 1) :=
    tendsto_nat_ceil_div_atTop.comp hpow
  have hlog : Tendsto (fun q : ℝ ↦ log ((⌈q ^ γ⌉₊ : ℝ) / q ^ γ)) atTop (𝓝 0) := by
    simpa using hratio.log one_ne_zero
  have herr := hlog.div_atTop tendsto_log_atTop
  have hsum := herr.add_const γ
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with q hq
  have hq₀ : 0 < q := lt_trans zero_lt_one hq
  have hqp : 0 < q ^ γ := rpow_pos_of_pos hq₀ γ
  have hceil : 0 < (⌈q ^ γ⌉₊ : ℝ) := lt_of_lt_of_le hqp (Nat.le_ceil _)
  rw [log_div hceil.ne' hqp.ne', log_rpow hq₀]
  field_simp [(log_pos hq).ne']
  ring

theorem tendsto_log_scale_natCeil_rpow_div_log {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ ↦ log ((⌈q ^ γ⌉₊ : ℝ) ^ (4 / 3 : ℝ)) / log q)
      atTop (𝓝 (4 * γ / 3)) := by
  have h := (tendsto_log_natCeil_rpow_div_log hγ).const_mul (4 / 3 : ℝ)
  have heq : (4 / 3 : ℝ) * γ = 4 * γ / 3 := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
  have hceil : 0 < (⌈q ^ γ⌉₊ : ℝ) :=
    lt_of_lt_of_le (rpow_pos_of_pos hq γ) (Nat.le_ceil _)
  rw [log_rpow hceil]
  ring

theorem tendsto_natCeil_rpow_atTop {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ ↦ ⌈q ^ γ⌉₊) atTop atTop :=
  tendsto_nat_ceil_atTop.comp (tendsto_rpow_atTop hγ)

theorem tendsto_scale_natCeil_rpow_atTop {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ ↦ (⌈q ^ γ⌉₊ : ℝ) ^ (4 / 3 : ℝ)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 3)).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_natCeil_rpow_atTop hγ))

theorem exists_gamma_second_term_bound (C : ℝ) :
    ∃ γ : ℝ, 0 < γ ∧ (C + 13 / 24) / (4 * γ / 3) < 1 / 16 := by
  refine ⟨12 * (|C| + 1), by positivity, ?_⟩
  have hC : C ≤ |C| := le_abs_self C
  rw [div_lt_iff₀ (by positivity : 0 < 4 * (12 * (|C| + 1)) / 3)]
  linarith

theorem scale_cube_eq_degree_four {N : ℝ} (hN : 0 ≤ N) :
    (N ^ (4 / 3 : ℝ)) ^ (3 : ℕ) = N ^ (4 : ℕ) := by
  rw [← rpow_mul_natCast hN]
  norm_num

theorem log_degree_four_eq_three_log_scale {N : ℝ} (hN : 0 < N) :
    log (N ^ (4 : ℕ)) = 3 * log (N ^ (4 / 3 : ℝ)) := by
  rw [log_pow, log_rpow hN]
  ring

theorem log_eq_three_quarters_log_scale {N : ℝ} (hN : 0 < N) :
    log N = (3 / 4 : ℝ) * log (N ^ (4 / 3 : ℝ)) := by
  rw [log_rpow hN]
  ring

end WeightedTorusJets

end

section
namespace WeightedTorusJets

theorem weight_rpow_shift {H : ℝ} (hH : 0 < H) :
    H ^ (-1 / 3 : ℝ) * H = H ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_add_one hH.ne']
  norm_num

theorem rectangle_weight_sum {H U : ℝ} (hH : 0 < H) :
    32 * H ^ (2 / 3 : ℝ) * U + H * (32 * H ^ (-1 / 3 : ℝ) * U) +
      H * (32 * H ^ (-1 / 3 : ℝ) * U) = 96 * H ^ (2 / 3 : ℝ) * U := by
  rw [← weight_rpow_shift hH]
  ring

theorem rectangle_weight_le {H U a₁ a₂ a₃ : ℝ} (hH : 0 < H)
    (ha₁ : a₁ ≤ 32 * H ^ (2 / 3 : ℝ) * U)
    (ha₂ : a₂ ≤ 32 * H ^ (-1 / 3 : ℝ) * U)
    (ha₃ : a₃ ≤ 32 * H ^ (-1 / 3 : ℝ) * U) :
    a₁ + H * a₂ + H * a₃ ≤ 96 * H ^ (2 / 3 : ℝ) * U := by
  rw [← rectangle_weight_sum hH]
  exact add_le_add (add_le_add ha₁ (mul_le_mul_of_nonneg_left ha₂ hH.le))
    (mul_le_mul_of_nonneg_left ha₃ hH.le)

theorem transverse_coordinates_le {H U a₁ a₂ a₃ : ℝ} (hH : 0 < H)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
    (hw : a₁ + H * a₂ + H * a₃ ≤ 96 * H ^ (2 / 3 : ℝ) * U) :
    a₂ ≤ 96 * H ^ (-1 / 3 : ℝ) * U ∧
      a₃ ≤ 96 * H ^ (-1 / 3 : ℝ) * U := by
  have hbound : 96 * H ^ (2 / 3 : ℝ) * U =
      H * (96 * H ^ (-1 / 3 : ℝ) * U) := by rw [← weight_rpow_shift hH]; ring
  rw [hbound] at hw
  constructor
  · exact (mul_le_mul_iff_right₀ hH).mp (by nlinarith)
  · exact (mul_le_mul_iff_right₀ hH).mp (by nlinarith)

theorem pivot_ratio_le {H M U S₁ S₂ : ℝ} (hH : 0 < H) (hM : 0 < M)
    (hU : 0 < U)
    (hS₁ : M * H ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2) ≤ S₁)
    (hS₂ : S₂ ≤ 192 * M * H ^ (-1 / 3 : ℝ) * U) :
    S₂ / S₁ ≤ 7226112 / H := by
  have hpow : 0 < H ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hH _
  have hS₁pos : 0 < S₁ := lt_of_lt_of_le (by positivity) hS₁
  rw [div_le_div_iff₀ hS₁pos hH]
  have hmul := mul_le_mul_of_nonneg_right hS₂ hH.le
  have hlower := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4 * 97 ^ 2)).mp hS₁
  calc
    S₂ * H ≤ 192 * M * H ^ (-1 / 3 : ℝ) * U * H := hmul
    _ = 192 * (M * H ^ (2 / 3 : ℝ) * U) := by rw [← weight_rpow_shift hH]; ring
    _ ≤ 7226112 * S₁ := by nlinarith

theorem pivot_ratio_le_one_twelfth {H M U S₁ S₂ : ℝ} (hH : 86713344 ≤ H)
    (hM : 0 < M) (hU : 0 < U)
    (hS₁ : M * H ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2) ≤ S₁)
    (hS₂ : S₂ ≤ 192 * M * H ^ (-1 / 3 : ℝ) * U) :
    S₂ / S₁ ≤ 1 / 12 := by
  have hHpos : 0 < H := by linarith
  exact (pivot_ratio_le hHpos hM hU hS₁ hS₂).trans
    ((div_le_iff₀ hHpos).mpr (by linarith))

theorem floor_square_bound {t : ℝ} (ht : 1 ≤ t) :
    ((⌊96 * t⌋₊ : ℝ) + 1) ^ 2 ≤ 97 ^ 2 * t ^ 2 := by
  have hfloor := Nat.floor_le (by linarith : 0 ≤ 96 * t)
  have hfloorpos : 0 ≤ (⌊96 * t⌋₊ : ℝ) := Nat.cast_nonneg _
  have hbound : (⌊96 * t⌋₊ : ℝ) + 1 ≤ 97 * t := by linarith
  nlinarith

theorem transverse_scale_ge {H N : ℝ} (hH : 0 < H) (hHN : H ≤ N) :
    N ≤ H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) := by
  have hN : 0 < N := hH.trans_le hHN
  have hmono := Real.rpow_le_rpow hH.le hHN (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hroot : 0 < H ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hH _
  have hNpow : N ^ (4 / 3 : ℝ) = N * N ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hN, Real.rpow_one]
  rw [show (-1 / 3 : ℝ) = -(1 / 3 : ℝ) by ring, Real.rpow_neg hH.le, hNpow]
  calc
    N = (H ^ (1 / 3 : ℝ))⁻¹ * (N * H ^ (1 / 3 : ℝ)) := by field_simp
    _ ≤ (H ^ (1 / 3 : ℝ))⁻¹ * (N * N ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hN.le) (inv_nonneg.mpr hroot.le)

theorem pivot_floor_square_rpow_bound {H N : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N) :
    ((⌊96 * H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ)⌋₊ : ℝ) + 1) ^ 2 ≤
      97 ^ 2 * H ^ (-2 / 3 : ℝ) * (N ^ (4 / 3 : ℝ)) ^ 2 := by
  have hHpos : 0 < H := by linarith
  have hscale := (hH.trans hHN).trans (transverse_scale_ge hHpos hHN)
  have hbound := floor_square_bound hscale
  have hpow : (H ^ (-1 / 3 : ℝ)) ^ 2 = H ^ (-2 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast hHpos.le]
    norm_num
  simpa only [mul_assoc, mul_pow, hpow] using hbound

theorem twice_pivot_floor_square_le {H N : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (hNlarge : 18818 ≤ N) :
    2 * (((⌊96 * H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ)⌋₊ : ℝ) + 1) ^ 2) ≤
      N ^ 4 := by
  have hN : 0 ≤ N := by linarith
  have hbound := pivot_floor_square_rpow_bound hH hHN
  have hp : H ^ (-2 / 3 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hH (by norm_num)
  have hpbound : 97 ^ 2 * H ^ (-2 / 3 : ℝ) * (N ^ (4 / 3 : ℝ)) ^ 2 ≤
      97 ^ 2 * (N ^ (4 / 3 : ℝ)) ^ 2 := by nlinarith [sq_nonneg (N ^ (4 / 3 : ℝ))]
  have hNU : N ≤ N ^ (4 / 3 : ℝ) :=
    Real.self_le_rpow_of_one_le (by linarith) (by norm_num)
  have hM := scale_cube_eq_degree_four hN
  have hlarge := mul_le_mul_of_nonneg_right (hNlarge.trans hNU)
    (sq_nonneg (N ^ (4 / 3 : ℝ)))
  nlinarith

end WeightedTorusJets

end

section
open Filter
open scoped Topology

namespace WeightedTorusJets

theorem normalized_error_component_bounds {M U S A : ℝ}
    (hM : 0 < M) (hU : 1 < U) (hA : 0 < A)
    (hS : A * M * U ≤ S) (hlog : Real.log M = 3 * Real.log U) :
    M * U / (S * Real.log U) ≤ 1 / (A * Real.log U) ∧
      M * Real.log M / (S * Real.log U) ≤ 3 / (A * U) := by
  have hU0 : 0 < U := lt_trans zero_lt_one hU
  have hL : 0 < Real.log U := Real.log_pos hU
  have hden : 0 < A * M * U * Real.log U := by positivity
  have hden_le : A * M * U * Real.log U ≤ S * Real.log U :=
    mul_le_mul_of_nonneg_right hS hL.le
  constructor
  · calc
      M * U / (S * Real.log U) ≤ M * U / (A * M * U * Real.log U) :=
        div_le_div_of_nonneg_left (by positivity) hden hden_le
      _ = _ := by field_simp
  · have hnum : 0 ≤ M * Real.log M := by rw [hlog]; positivity
    calc
      M * Real.log M / (S * Real.log U) ≤
          M * Real.log M / (A * M * U * Real.log U) :=
        div_le_div_of_nonneg_left hnum hden hden_le
      _ = _ := by rw [hlog]; field_simp

theorem normalized_error_component_bounds_weighted {M U S H : ℝ}
    (hM : 0 < M) (hU : 1 < U) (hH : 0 < H)
    (hS : M * H ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2) ≤ S)
    (hlog : Real.log M = 3 * Real.log U) :
    M * U / (S * Real.log U) ≤ 37636 * H ^ (-(2 / 3 : ℝ)) / Real.log U ∧
      M * Real.log M / (S * Real.log U) ≤ 112908 * H ^ (-(2 / 3 : ℝ)) / U := by
  have hA : 0 < H ^ (2 / 3 : ℝ) / 37636 := by positivity
  have hS' : H ^ (2 / 3 : ℝ) / 37636 * M * U ≤ S := by
    convert hS using 1
    ring
  obtain ⟨hfirst, hsecond⟩ := normalized_error_component_bounds hM hU hA hS' hlog
  constructor
  · convert hfirst using 1
    rw [Real.rpow_neg hH.le]
    field_simp
  · convert hsecond using 1
    rw [Real.rpow_neg hH.le]
    field_simp
    norm_num

theorem determinant_error_le {M U S A C : ℝ}
    (hM : 0 < M) (hU : 1 < U) (hA : 0 < A) (hC : 0 ≤ C)
    (hS : A * M * U ≤ S) (hlog : Real.log M = 3 * Real.log U) :
    (C * M * U + (1 / 2 : ℝ) * M * Real.log M) / (S * Real.log U) ≤
      C / (A * Real.log U) + 3 / (2 * A * U) := by
  obtain ⟨hfirst, hsecond⟩ := normalized_error_component_bounds hM hU hA hS hlog
  calc
    _ = C * (M * U / (S * Real.log U)) +
        (1 / 2 : ℝ) * (M * Real.log M / (S * Real.log U)) := by ring
    _ ≤ C * (1 / (A * Real.log U)) + (1 / 2 : ℝ) * (3 / (A * U)) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hC)
        (mul_le_mul_of_nonneg_left hsecond (by norm_num))
    _ = _ := by ring

theorem tendsto_determinant_error {ι : Type*} {l : Filter ι}
    {M U S : ι → ℝ} {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hU : Tendsto U l atTop)
    (hM : ∀ᶠ n in l, 0 < M n)
    (hS : ∀ᶠ n in l, A * M n * U n ≤ S n)
    (hlog : ∀ᶠ n in l, Real.log (M n) = 3 * Real.log (U n)) :
    Tendsto (fun n =>
      (C * M n * U n + (1 / 2 : ℝ) * M n * Real.log (M n)) /
        (S n * Real.log (U n))) l (𝓝 0) := by
  have hU1 : ∀ᶠ n in l, 1 < U n := hU.eventually_gt_atTop 1
  have hbound : Tendsto (fun n =>
      C / (A * Real.log (U n)) + 3 / (2 * A * U n)) l (𝓝 0) := by
    have hL := Real.tendsto_log_atTop.comp hU
    have hfirst := (tendsto_const_nhds (x := C)).div_atTop (hL.const_mul_atTop hA)
    have hsecond := (tendsto_const_nhds (x := (3 : ℝ))).div_atTop
      (hU.const_mul_atTop (by positivity : 0 < 2 * A))
    simpa using hfirst.add hsecond
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [hM, hS, hlog, hU1] with n hMn hSn hlogn hUn
    have hL : 0 < Real.log (U n) := Real.log_pos hUn
    have hUn0 : 0 < U n := lt_trans zero_lt_one hUn
    have hSn0 : 0 < S n := lt_of_lt_of_le (by positivity) hSn
    rw [hlogn]
    positivity
  · filter_upwards [hM, hS, hlog, hU1] with n hMn hSn hlogn hUn
    exact determinant_error_le hMn hUn hA hC hSn hlogn

theorem tendsto_bounded_ratio_log_error {ι : Type*} {l : Filter ι}
    {r U : ι → ℝ} {R B K : ℝ} (hU : Tendsto U l atTop)
    (hr : ∀ᶠ n in l, |r n| ≤ R) :
    Tendsto (fun n => (B + (1 + r n) * K) / Real.log (U n)) l (𝓝 0) := by
  have hbound := (tendsto_const_nhds (x := |B| + (1 + R) * |K|)).div_atTop
    (Real.tendsto_log_atTop.comp hU)
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [hr, hU.eventually_gt_atTop 1] with n hrn hUn
  have hL : 0 < Real.log (U n) := Real.log_pos hUn
  simp only [Real.norm_eq_abs, abs_div, abs_of_pos hL]
  apply div_le_div_of_nonneg_right _ hL.le
  calc
    |B + (1 + r n) * K| ≤ |B| + |(1 + r n) * K| := abs_add_le _ _
    _ = |B| + |1 + r n| * |K| := by rw [abs_mul]
    _ ≤ |B| + (1 + R) * |K| := by
      have hsum : |1 + r n| ≤ 1 + R := by
        calc
          _ ≤ |(1 : ℝ)| + |r n| := abs_add_le _ _
          _ ≤ 1 + R := by simpa using add_le_add_left hrn 1
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsum (abs_nonneg K))

theorem tendsto_normalized_error_sum {ι : Type*} {l : Filter ι}
    {M U S₁ S₂ δ ℓ : ι → ℝ} {A C C_H a : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hU : Tendsto U l atTop) (hδ : Tendsto δ l (𝓝 0))
    (hquot : Tendsto (fun n => Real.log (U n) / ℓ n) l (𝓝 a))
    (hM : ∀ᶠ n in l, 0 < M n)
    (hS₁ : ∀ᶠ n in l, A * M n * U n ≤ S₁ n)
    (hS₂ : ∀ᶠ n in l, 0 ≤ S₂ n)
    (hr : ∀ᶠ n in l, S₂ n / S₁ n ≤ 1 / 12)
    (hlog : ∀ᶠ n in l, Real.log (M n) = 3 * Real.log (U n)) :
    Tendsto (fun n =>
      C * δ n * (Real.log (U n) / ℓ n) +
      (C_H + (1 + S₂ n / S₁ n) * Real.log 8) / Real.log (U n) +
      (C * M n * U n + (1 / 2 : ℝ) * M n * Real.log (M n)) /
        (S₁ n * Real.log (U n))) l (𝓝 0) := by
  have hrabs : ∀ᶠ n in l, |S₂ n / S₁ n| ≤ 1 / 12 := by
    filter_upwards [hM, hS₁, hS₂, hr, hU.eventually_gt_atTop 0]
      with n hMn hS₁n hS₂n hrn hUn
    have hS₁pos : 0 < S₁ n := lt_of_lt_of_le (by positivity) hS₁n
    rwa [abs_of_nonneg (div_nonneg hS₂n hS₁pos.le)]
  have hfirst := (hδ.const_mul C).mul hquot
  have hsecond := tendsto_bounded_ratio_log_error (B := C_H) (K := Real.log 8) hU hrabs
  have hthird := tendsto_determinant_error hA hC hU hM hS₁ hlog
  simpa using (hfirst.add hsecond).add hthird

end WeightedTorusJets

end

section
namespace WeightedTorusJets.FinalComparison

theorem uniform_master_bound {L M U ℓ S₁ S₂ δ C C_H D : ℝ}
    (hM : 0 < M) (hU : 1 < U) (hℓ : 0 < ℓ) (hD : 0 < D) (hC : 0 ≤ C)
    (hS₁ : D * M * U ≤ S₁) (hr : S₂ / S₁ ≤ 1 / 12)
    (hlogM : Real.log M = 3 * Real.log U)
    (hupper : L ≤ M / 2 * Real.log M +
      (S₁ + S₂) * (3 / 4 * Real.log U + 1 / 2 * ℓ + Real.log 8))
    (hlower : S₁ * (Real.log U - C * ℓ - C * δ * Real.log U ^ 2 / ℓ - C_H) -
      C * M * U ≤ L) :
    1 ≤ 13 / 16 + (C + 13 / 24) * (ℓ / Real.log U) +
      C * δ * (Real.log U / ℓ) + (C_H + 13 / 12 * Real.log 8) / Real.log U +
      C / (D * Real.log U) + 3 / (2 * D * U) := by
  have hUpos : 0 < U := zero_lt_one.trans hU
  have hlogU : 0 < Real.log U := Real.log_pos hU
  have hS₁pos : 0 < S₁ := lt_of_lt_of_le (by positivity) hS₁
  have hmaster := normalized_master_bound hS₁pos hlogU hℓ rfl hupper hlower
  have hfirst : 3 / 4 * (1 + S₂ / S₁) ≤ (13 : ℝ) / 16 := by linarith
  have hsecond : (C + 1 / 2 * (1 + S₂ / S₁)) * (ℓ / Real.log U) ≤
      (C + 13 / 24) * (ℓ / Real.log U) :=
    mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hℓ.le hlogU.le)
  have hfixed : (C_H + (1 + S₂ / S₁) * Real.log 8) / Real.log U ≤
      (C_H + 13 / 12 * Real.log 8) / Real.log U := by
    apply (div_le_div_iff_of_pos_right hlogU).mpr
    have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have := mul_le_mul_of_nonneg_right (by linarith : 1 + S₂ / S₁ ≤ 13 / 12) hlog8
    linarith
  have hdet := WeightedTorusJets.determinant_error_le hM hU hD hC hS₁ hlogM
  linarith

end WeightedTorusJets.FinalComparison

end

section
namespace WeightedTorusJets

open Filter Topology

theorem exists_fixed_parameters_not_eventually_uniform_bound (C : ℝ) :
    ∃ H : ℕ, 86713344 ≤ H ∧ ∃ γ : ℝ, 0 < γ ∧
      ∀ (q δ : ℕ → ℝ) (C_H : ℝ),
        Tendsto q atTop atTop → Tendsto δ atTop (𝓝 0) →
        let N : ℕ → ℝ := fun k ↦ (⌈q k ^ γ⌉₊ : ℝ)
        let U : ℕ → ℝ := fun k ↦ N k ^ (4 / 3 : ℝ)
        let D : ℝ := (H : ℝ) ^ (2 / 3 : ℝ) / (4 * 97 ^ 2)
        ¬ (∀ᶠ k in atTop,
          1 ≤ 13 / 16 + (C + 13 / 24) * (Real.log (q k) / Real.log (U k)) +
            C * δ k * (Real.log (U k) / Real.log (q k)) +
            (C_H + 13 / 12 * Real.log 8) / Real.log (U k) +
            C / (D * Real.log (U k)) + 3 / (2 * D * U k)) := by
  obtain ⟨γ, hγ, hchoice⟩ := exists_gamma_second_term_bound C
  refine ⟨86713344, le_rfl, γ, hγ, ?_⟩
  intro q δ C_H hq hδ N U D hbound
  have hD : 0 < D := by dsimp [D]; positivity
  have hU : Tendsto U atTop atTop := (tendsto_scale_natCeil_rpow_atTop hγ).comp hq
  have hlogU := Real.tendsto_log_atTop.comp hU
  have hratio : Tendsto (fun k ↦ Real.log (U k) / Real.log (q k))
      atTop (𝓝 (4 * γ / 3)) := (tendsto_log_scale_natCeil_rpow_div_log hγ).comp hq
  have hδterm : Tendsto (fun k ↦ C * δ k * (Real.log (U k) / Real.log (q k)))
      atTop (𝓝 0) := by simpa using (hδ.const_mul C).mul hratio
  have hfixed := (tendsto_const_nhds (x := C_H + 13 / 12 * Real.log 8)).div_atTop hlogU
  have hdet₁ := (tendsto_const_nhds (x := C)).div_atTop (hlogU.const_mul_atTop hD)
  have hdet₂ := (tendsto_const_nhds (x := (3 : ℝ))).div_atTop
    (hU.const_mul_atTop (by positivity : 0 < 2 * D))
  have herror : Tendsto (fun k ↦ C * δ k * (Real.log (U k) / Real.log (q k)) +
      (C_H + 13 / 12 * Real.log 8) / Real.log (U k) + C / (D * Real.log (U k)) +
      3 / (2 * D * U k)) atTop (𝓝 0) := by
    simpa using ((hδterm.add hfixed).add hdet₁).add hdet₂
  apply FinalComparison.not_eventually_master (r := fun _ ↦ (1 / 12 : ℝ))
    (by positivity) hchoice.le (.of_forall fun _ ↦ le_rfl) hratio herror
  filter_upwards [hbound] with k hk
  simpa only [show (3 / 4 : ℝ) * (1 + 1 / 12) = 13 / 16 by norm_num,
    show (1 / 2 : ℝ) * (1 + 1 / 12) = 13 / 24 by norm_num,
    div_div_eq_mul_div, mul_div_assoc, add_assoc] using hk

end WeightedTorusJets

end

end

end SiegelZeros

end OAI
