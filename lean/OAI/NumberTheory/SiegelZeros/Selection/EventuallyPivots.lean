import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import OAI.NumberTheory.SiegelZeros.Estimates.AsymptoticAssembly
import OAI.NumberTheory.SiegelZeros.Structure.FiberCount

namespace OAI

namespace SiegelZeros

section

open scoped BigOperators

namespace WeightedTorusJets.W32

theorem count_lt_le {ι : Type*} (s : Finset ι) (a : ι → ℕ) (Q t : ℕ)
    (hQ : ∀ n, (s.filter (fun i => a i = n)).card ≤ Q) :
    (s.filter (fun i => a i < t)).card ≤ Q * t := by
  classical
  have hf := Finset.sum_card_fiberwise_eq_card_filter s (Finset.range t) a
  simp only [Finset.mem_range] at hf
  rw [← hf]
  calc
    ∑ n ∈ Finset.range t, (s.filter (fun i => a i = n)).card
      ≤ ∑ _n ∈ Finset.range t, Q := Finset.sum_le_sum (fun n _ => hQ n)
    _ = Q * t := by simp [Nat.mul_comm]

theorem pair_count_identity {ι : Type*} (s : Finset ι) (a : ι → ℕ) :
    2 * (∑ i ∈ s, (s.filter (fun j => a j < a i)).card) +
      (∑ i ∈ s, (s.filter (fun j => a j = a i)).card) = s.card ^ 2 := by
  classical
  have hpoint (i j : ι) :
      (if a j < a i then 1 else 0) + (if a i < a j then 1 else 0) +
        (if a j = a i then 1 else 0) = (1 : ℕ) := by
    split_ifs <;> omega
  have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ s) =>
    Finset.sum_congr rfl (fun j (_ : j ∈ s) => hpoint i j))
  have hswap :
      (∑ i ∈ s, ∑ j ∈ s, if a i < a j then 1 else 0) =
      (∑ i ∈ s, ∑ j ∈ s, if a j < a i then 1 else 0) := by
    rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib] at hsum
  rw [hswap] at hsum
  simp only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  nlinarith [hsum]

theorem occupancy_nat {ι : Type*} (s : Finset ι) (a : ι → ℕ) (Q : ℕ)
    (hQ : ∀ n, (s.filter (fun i => a i = n)).card ≤ Q) :
    s.card ^ 2 ≤ Q * (2 * (∑ i ∈ s, a i) + s.card) := by
  classical
  have hlt : (∑ i ∈ s, (s.filter (fun j => a j < a i)).card) ≤
      Q * (∑ i ∈ s, a i) := by
    calc
      _ ≤ ∑ i ∈ s, Q * a i :=
        Finset.sum_le_sum (fun i _ => count_lt_le s a Q (a i) hQ)
      _ = _ := by rw [Finset.mul_sum]
  have heq : (∑ i ∈ s, (s.filter (fun j => a j = a i)).card) ≤ Q * s.card := by
    calc
      _ ≤ ∑ _i ∈ s, Q := Finset.sum_le_sum (fun i _ => hQ (a i))
      _ = _ := by simp [Nat.mul_comm]
  have hid := pair_count_identity s a
  nlinarith

theorem occupancy_real {ι : Type*} (s : Finset ι) (a : ι → ℕ) (Q : ℕ)
    (hpos : 0 < Q)
    (hQ : ∀ n, (s.filter (fun i => a i = n)).card ≤ Q) :
    (s.card : ℝ) ^ 2 / (2 * (Q : ℝ)) - (s.card : ℝ) / 2 ≤
      ∑ i ∈ s, (a i : ℝ) := by
  classical
  have hnat := occupancy_nat s a Q hQ
  have hreal : (s.card : ℝ) ^ 2 ≤
      (Q : ℝ) * (2 * (∑ i ∈ s, (a i : ℝ)) + (s.card : ℝ)) := by
    exact_mod_cast hnat
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hpos
  apply (sub_le_iff_le_add).2
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (Q : ℝ))).2
  nlinarith

end WeightedTorusJets.W32

end


namespace Result.Workers.W33

noncomputable def occupancyCap (t : ℝ) : ℝ := ((Nat.floor (96 * t) : ℝ) + 1) ^ 2

theorem occupancyCap_pos (t : ℝ) : 0 < occupancyCap t := by
  unfold occupancyCap
  positivity

theorem occupancyCap_le {t : ℝ} (ht : 1 ≤ t) :
    occupancyCap t ≤ 97 ^ 2 * t ^ 2 := by
  have hf := Nat.floor_le (show 0 ≤ 96 * t by linarith)
  have hb : (Nat.floor (96 * t) : ℝ) + 1 ≤ 97 * t := by linarith
  have hn : 0 ≤ (Nat.floor (96 * t) : ℝ) + 1 := by positivity
  have hp := mul_self_le_mul_self hn hb
  unfold occupancyCap
  nlinarith

theorem occupancy_lower_strengthen {M Q S : ℝ} (hQ : 0 < Q) (hM : 2 * Q ≤ M)
    (hS : M ^ 2 / (2 * Q) - M / 2 ≤ S) : M ^ 2 / (4 * Q) ≤ S := by
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  have hprod : 2 * M * Q ≤ M ^ 2 := by nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hM)]
  have haux : M ^ 2 / (4 * Q) ≤ M ^ 2 / (2 * Q) - M / 2 := by
    apply (div_le_iff₀ (show 0 < 4 * Q by positivity)).2
    have he : (M ^ 2 / (2 * Q) - M / 2) * (4 * Q) =
        2 * M ^ 2 - 2 * M * Q := by
      field_simp
      ring
    rw [he]
    nlinarith
  exact haux.trans hS

theorem negative_third_squared {H : ℝ} (hH : 0 < H) :
    (H ^ (-(1 / 3 : ℝ))) ^ (2 : ℕ) = H ^ (-(2 / 3 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hH.le]
  congr 1
  norm_num

theorem negative_two_thirds_cancel {H : ℝ} (hH : 0 < H) :
    H ^ (-(2 / 3 : ℝ)) * H ^ (2 / 3 : ℝ) = 1 := by
  rw [← Real.rpow_add hH]
  norm_num

theorem negative_third_mul_self {H : ℝ} (hH : 0 < H) :
    H ^ (-(1 / 3 : ℝ)) * H = H ^ (2 / 3 : ℝ) := by
  nth_rw 2 [← Real.rpow_one H]
  rw [← Real.rpow_add hH]
  congr 1
  norm_num

theorem source_scale_ge_one {H N : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N) :
    1 ≤ H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ) := by
  have hH0 : 0 < H := by linarith
  have hp := Real.rpow_le_rpow hH0.le hHN (show (0 : ℝ) ≤ 4 / 3 by norm_num)
  have hm := mul_le_mul_of_nonneg_left hp
    (Real.rpow_nonneg hH0.le (-(1 / 3 : ℝ)))
  have he : H ^ (-(1 / 3 : ℝ)) * H ^ (4 / 3 : ℝ) = H := by
    rw [← Real.rpow_add hH0]
    norm_num
  rw [he] at hm
  exact hH.trans hm

theorem source_occupancyCap_le {H N : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N) :
    occupancyCap (H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ)) ≤
      97 ^ 2 * H ^ (-(2 / 3 : ℝ)) * (N ^ (4 / 3 : ℝ)) ^ (2 : ℕ) := by
  have h := occupancyCap_le (source_scale_ge_one hH hHN)
  rw [mul_pow, negative_third_squared (by linarith : 0 < H)] at h
  simpa [mul_assoc] using h

theorem source_dimension {N : ℝ} (hN : 0 ≤ N) :
    (N ^ (4 / 3 : ℝ)) ^ (3 : ℕ) = N ^ (4 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
  norm_num

theorem source_twice_occupancyCap_le {H N : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (hN : 18818 ≤ N) :
    2 * occupancyCap (H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ)) ≤ N ^ (4 : ℕ) := by
  have hH0 : 0 < H := by linarith
  have hN1 : 1 ≤ N := hH.trans hHN
  have hN0 : 0 ≤ N := by linarith
  have hpow : H ^ (-(2 / 3 : ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hH
      (show -(2 / 3 : ℝ) ≤ 0 by norm_num)
  have hU : N ≤ N ^ (4 / 3 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1
      (show (1 : ℝ) ≤ 4 / 3 by norm_num)
  have hcap := source_occupancyCap_le hH hHN
  have hs := sq_nonneg (N ^ (4 / 3 : ℝ))
  have hc : occupancyCap (H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ)) ≤
      9409 * (N ^ (4 / 3 : ℝ)) ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hs]
  rw [← source_dimension hN0]
  nlinarith [mul_nonneg (show 0 ≤ N ^ (4 / 3 : ℝ) - 18818 by linarith) hs]

theorem eventually_twice_occupancyCap_le (H : ℕ) (hH : 1 ≤ H) :
    ∀ᶠ N : ℕ in Filter.atTop,
      2 * occupancyCap ((H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)) ≤
        (N : ℝ) ^ (4 : ℕ) := by
  filter_upwards [Filter.eventually_ge_atTop (max H 18818)] with N hN
  apply source_twice_occupancyCap_le
  · exact_mod_cast hH
  · exact_mod_cast (le_max_left H 18818).trans hN
  · exact_mod_cast (le_max_right H 18818).trans hN

theorem source_pivot_lower {H N S₁ : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (hN : 18818 ≤ N)
    (hocc : (N ^ (4 : ℕ)) ^ (2 : ℕ) /
        (2 * occupancyCap (H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ))) -
        N ^ (4 : ℕ) / 2 ≤ S₁) :
    N ^ (4 : ℕ) * H ^ (2 / 3 : ℝ) * N ^ (4 / 3 : ℝ) / (4 * 97 ^ 2) ≤ S₁ := by
  have hH0 : 0 < H := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hU0 : 0 ≤ N ^ (4 / 3 : ℝ) := Real.rpow_nonneg hN0 _
  let Q := occupancyCap (H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ))
  have hQ : 0 < Q := occupancyCap_pos _
  have hs := occupancy_lower_strengthen hQ (source_twice_occupancyCap_le hH hHN hN) hocc
  apply le_trans _ hs
  apply (le_div_iff₀ (show 0 < 4 * Q by positivity)).2
  have hc := source_occupancyCap_le hH hHN
  have hm := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ N ^ (4 : ℕ) * H ^ (2 / 3 : ℝ) * N ^ (4 / 3 : ℝ) / (97 ^ 2) by positivity)
  have hid : (N ^ (4 : ℕ) * H ^ (2 / 3 : ℝ) * N ^ (4 / 3 : ℝ) / (97 ^ 2)) *
      (97 ^ 2 * H ^ (-(2 / 3 : ℝ)) * (N ^ (4 / 3 : ℝ)) ^ (2 : ℕ)) =
      (N ^ (4 : ℕ)) ^ (2 : ℕ) := by
    calc
      _ = N ^ (4 : ℕ) * (H ^ (-(2 / 3 : ℝ)) * H ^ (2 / 3 : ℝ)) *
          (N ^ (4 / 3 : ℝ)) ^ (3 : ℕ) := by ring
      _ = _ := by rw [negative_two_thirds_cancel hH0, source_dimension hN0]; ring
  rw [hid] at hm
  change _ * (4 * occupancyCap _) ≤ _
  nlinarith

theorem pivot_ratio {H M U S₁ S₂ : ℝ} (hH : 0 < H) (hM : 0 < M)
    (hU : 0 < U)
    (hS₁ : M * H ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2) ≤ S₁)
    (hS₂ : S₂ ≤ 192 * M * H ^ (-(1 / 3 : ℝ)) * U) :
    S₂ / S₁ ≤ 7226112 / H := by
  have hS₁pos : 0 < S₁ := lt_of_lt_of_le (by positivity) hS₁
  have hm := mul_le_mul_of_nonneg_right hS₂ hH.le
  have hid : (192 * M * H ^ (-(1 / 3 : ℝ)) * U) * H =
      192 * M * H ^ (2 / 3 : ℝ) * U := by
    calc
      _ = 192 * M * (H ^ (-(1 / 3 : ℝ)) * H) * U := by ring
      _ = _ := by rw [negative_third_mul_self hH]
  rw [hid] at hm
  apply (div_le_iff₀ hS₁pos).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hH).2
  nlinarith

end Result.Workers.W33


section

open scoped BigOperators

namespace Result.Workers.W33

theorem finite_pivot_lower {ι : Type*} (s : Finset ι) (a : ι → ℕ) (H N : ℕ)
    (hH : 1 ≤ H) (hHN : H ≤ N) (hN : 18818 ≤ N) (hcard : s.card = N ^ 4)
    (hcap : ∀ k, (s.filter (fun i => a i = k)).card ≤
      (Nat.floor (96 * ((H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ))) + 1) ^ 2) :
    (N : ℝ) ^ (4 : ℕ) * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) /
      (4 * 97 ^ 2) ≤ ∑ i ∈ s, (a i : ℝ) := by
  classical
  apply source_pivot_lower (by exact_mod_cast hH) (by exact_mod_cast hHN)
    (by exact_mod_cast hN)
  have h := WeightedTorusJets.W32.occupancy_real s a
    ((Nat.floor (96 * ((H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ))) + 1) ^ 2)
    (by positivity) hcap
  simpa [occupancyCap, hcard] using h

theorem cutoff_pivot_lower (P : Finset SiegelZerosAwei.W31.MultiIndex) (H N : ℕ)
    (hH : 1 ≤ H) (hHN : H ≤ N) (hN : 18818 ≤ N) (hcard : P.card = N ^ 4)
    (hcut : ∀ a ∈ P, SiegelZerosAwei.W31.weight (H : ℝ) a ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    (N : ℝ) ^ (4 : ℕ) * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) /
      (4 * 97 ^ 2) ≤ ∑ a ∈ P, (a 0 : ℝ) := by
  apply finite_pivot_lower P (fun a => a 0) H N hH hHN hN hcard
  intro k
  have hp : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  simpa [mul_assoc] using SiegelZerosAwei.W31.cutoff_fiber_card_le hp P hcut k

theorem cutoff_pivot_ratio (P : Finset SiegelZerosAwei.W31.MultiIndex) (H N : ℕ)
    (hH : 1 ≤ H) (hHN : H ≤ N) (hN : 18818 ≤ N) (hcard : P.card = N ^ 4)
    (hcut : ∀ a ∈ P, SiegelZerosAwei.W31.weight (H : ℝ) a ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    (∑ a ∈ P, ((a 1 : ℝ) + (a 2 : ℝ))) / (∑ a ∈ P, (a 0 : ℝ)) ≤
      7226112 / (H : ℝ) := by
  have hp : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply pivot_ratio hp (show 0 < (N : ℝ) ^ (4 : ℕ) by positivity)
    (Real.rpow_pos_of_pos hn _) (cutoff_pivot_lower P H N hH hHN hN hcard hcut)
  simpa only [hcard, Nat.cast_pow] using
    SiegelZerosAwei.W31.short_sum_le_192 hp (Real.rpow_nonneg hn.le _) P hcut

theorem cutoff_pivot_ratio_le_twelfth (P : Finset SiegelZerosAwei.W31.MultiIndex)
    (H N : ℕ) (hH : 86713344 ≤ H) (hHN : H ≤ N) (hcard : P.card = N ^ 4)
    (hcut : ∀ a ∈ P, SiegelZerosAwei.W31.weight (H : ℝ) a ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    (∑ a ∈ P, ((a 1 : ℝ) + (a 2 : ℝ))) / (∑ a ∈ P, (a 0 : ℝ)) ≤
      (1 / 12 : ℝ) := by
  have h := cutoff_pivot_ratio P H N (by omega) hHN (by omega) hcard hcut
  apply h.trans
  have hp : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  apply (div_le_iff₀ hp).2
  have hHr : (86713344 : ℝ) ≤ H := by exact_mod_cast hH
  linarith

end Result.Workers.W33

end


open Filter
open scoped BigOperators

namespace Result.Workers.W33

open WeightedTorusJets.W48

def firstOrder (P : Finset SiegelZerosAwei.W31.MultiIndex) : ℝ :=
  ∑ a ∈ P, (a 0 : ℝ)

def transverseOrder (P : Finset SiegelZerosAwei.W31.MultiIndex) : ℝ :=
  ∑ a ∈ P, ((a 1 : ℝ) + (a 2 : ℝ))

theorem eventual_pivot_bounds {ι : Type*} {l : Filter ι} {q : ι → ℕ}
    (P : ι → Finset SiegelZerosAwei.W31.MultiIndex) (H : ℕ) (hH : 1 ≤ H)
    {γ : ℝ} (hγ : 0 < γ) (hq : Tendsto q l atTop)
    (hcard : ∀ᶠ i in l, (P i).card = auxiliaryN γ (q i) ^ 4)
    (hcut : ∀ᶠ i in l, ∀ a ∈ P i, SiegelZerosAwei.W31.weight (H : ℝ) a ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * auxiliaryU γ (q i)) :
    ∀ᶠ i in l,
      H ≤ auxiliaryN γ (q i) ∧
      18818 ≤ auxiliaryN γ (q i) ∧
      0 < firstOrder (P i) ∧
      (auxiliaryN γ (q i) : ℝ) ^ (4 : ℕ) * (H : ℝ) ^ (2 / 3 : ℝ) *
        auxiliaryU γ (q i) / (4 * 97 ^ 2) ≤ firstOrder (P i) ∧
      transverseOrder (P i) ≤ 192 * (auxiliaryN γ (q i) : ℝ) ^ (4 : ℕ) *
        (H : ℝ) ^ (-(1 / 3 : ℝ)) * auxiliaryU γ (q i) ∧
      transverseOrder (P i) / firstOrder (P i) ≤ 7226112 / (H : ℝ) := by
  have hNt := (natural_conductor_limits hγ hq).1
  filter_upwards [hNt.eventually_ge_atTop (max H 18818), hcard, hcut] with i hn hc hw
  have hnH : H ≤ auxiliaryN γ (q i) := (le_max_left H 18818).trans hn
  have hnLarge : 18818 ≤ auxiliaryN γ (q i) := (le_max_right H 18818).trans hn
  have hHr : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hNr : (0 : ℝ) < auxiliaryN γ (q i) := by
    exact_mod_cast (show 0 < auxiliaryN γ (q i) by omega)
  have hlo := cutoff_pivot_lower (P i) H (auxiliaryN γ (q i)) hH hnH hnLarge hc hw
  have hhi := SiegelZerosAwei.W31.short_sum_le_192 hHr
    (Real.rpow_nonneg hNr.le (4 / 3 : ℝ)) (P i) hw
  have hratio := cutoff_pivot_ratio (P i) H (auxiliaryN γ (q i))
    hH hnH hnLarge hc hw
  refine ⟨hnH, hnLarge, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity) hlo
  · exact hlo
  · simpa only [transverseOrder, hc, Nat.cast_pow, auxiliaryU] using hhi
  · exact hratio

theorem eventual_pivot_ratio_le_twelfth {ι : Type*} {l : Filter ι} {q : ι → ℕ}
    (P : ι → Finset SiegelZerosAwei.W31.MultiIndex) (H : ℕ) (hH : 86713344 ≤ H)
    {γ : ℝ} (hγ : 0 < γ) (hq : Tendsto q l atTop)
    (hcard : ∀ᶠ i in l, (P i).card = auxiliaryN γ (q i) ^ 4)
    (hcut : ∀ᶠ i in l, ∀ a ∈ P i, SiegelZerosAwei.W31.weight (H : ℝ) a ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * auxiliaryU γ (q i)) :
    ∀ᶠ i in l, 0 < firstOrder (P i) ∧
      transverseOrder (P i) / firstOrder (P i) ≤ (1 / 12 : ℝ) := by
  have hb := eventual_pivot_bounds P H (by omega) hγ hq hcard hcut
  have hHr : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hsmall : 7226112 / (H : ℝ) ≤ (1 / 12 : ℝ) := by
    apply (div_le_iff₀ hHr).2
    have hHlarge : (86713344 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  filter_upwards [hb] with i hi
  exact ⟨hi.2.2.1, hi.2.2.2.2.2.trans hsmall⟩

theorem exists_fixed_weight :
    ∃ H : ℕ, 2 ≤ H ∧ ∀ {ι : Type*} {l : Filter ι} {q : ι → ℕ}
      (P : ι → Finset SiegelZerosAwei.W31.MultiIndex) {γ : ℝ},
      0 < γ → Tendsto q l atTop →
      (∀ᶠ i in l, (P i).card = auxiliaryN γ (q i) ^ 4) →
      (∀ᶠ i in l, ∀ a ∈ P i, SiegelZerosAwei.W31.weight (H : ℝ) a ≤
        96 * (H : ℝ) ^ (2 / 3 : ℝ) * auxiliaryU γ (q i)) →
      ∀ᶠ i in l, 0 < firstOrder (P i) ∧
        transverseOrder (P i) / firstOrder (P i) ≤ (1 / 12 : ℝ) := by
  refine ⟨86713344, by norm_num, ?_⟩
  intro ι l q P γ hγ hq hcard hcut
  exact eventual_pivot_ratio_le_twelfth P 86713344 le_rfl hγ hq hcard hcut

end Result.Workers.W33


end SiegelZeros

end OAI
