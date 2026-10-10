import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.RealEnergyLogMajorants
import OAI.NumberTheory.Catalan.Estimates.RealEnergyDampedDual
import OAI.NumberTheory.Catalan.Estimates.RealEnergyDiagonalSums

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Set

theorem energy_damping_log_cost {e r : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hrlo : (1 - e) ^ 2 ≤ r) (hrhi : r ≤ 1) : -Real.log r ≤ 4 * e := by
  have hrhalf : (1 / 2 : ℝ) ≤ r := by nlinarith [sq_nonneg e, he.1, he.2]
  have hr0 : 0 < r := by linarith
  have hgap : 1 - r ≤ 2 * e := by nlinarith [sq_nonneg e]
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hr0)
  rw [Real.log_inv] at hl
  have hi : r⁻¹ - 1 = (1 - r) / r := by field_simp [hr0.ne']
  rw [hi] at hl
  apply hl.trans
  apply (div_le_iff₀ hr0).mpr
  have hp := mul_le_mul_of_nonneg_left hrhalf (show 0 ≤ 4 * e by linarith [he.1])
  nlinarith

theorem realEnergy_cosine_tau_le {e u v : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) (huv : u ≠ v) :
    Real.log |u - v| ≤ realEnergyCosineKernel (realEnergyTau e ^ 2) u v + 4 * e := by
  have ht := realEnergyTau_bounds he
  have htlo : (1 - e) ^ 2 ≤ realEnergyTau e ^ 2 := le_rfl
  have hthi : realEnergyTau e ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2.le)]
  have hc := realEnergyCosineKernel_compare hu hv huv (sq_pos_of_pos ht.1)
  have hec := energy_damping_log_cost he htlo hthi
  linarith

theorem realEnergy_cosine_sigma_le {e s t : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) (hst : s ≠ t) :
    Real.log |s - t| ≤
      realEnergyCosineKernel (realEnergySigma e s * realEnergySigma e t) s t + 4 * e := by
  have hr := realEnergySigma_mul_bounds he hs ht
  have hr0 := mul_pos (realEnergySigma_mem he hs).1 (realEnergySigma_mem he ht).1
  have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], hs.2.le⟩
  have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2.le⟩
  have hc := realEnergyCosineKernel_compare hs' ht' hst hr0
  have hec := energy_damping_log_cost he hr.1 hr.2.le
  linarith

end

section

open Polynomial
open scoped BigOperators

private theorem trial_scalar_norm_le (a b : ℝ) {m : ℕ}
    (hm : 0 < m) (hb : |b| ≤ 1) : ‖a * b / (m : ℝ)‖ ≤ |a| := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [norm_div, norm_mul]
  simp only [Real.norm_eq_abs, abs_of_pos hm0]
  calc
    _ ≤ |a| * 1 / (m : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (abs_nonneg a)) hm0.le
    _ = |a| / (m : ℝ) := by rw [mul_one]
    _ ≤ |a| := div_le_self (abs_nonneg a) hm1

private theorem trial_abs_tail_le (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    (∑' k : ℕ, |u (k + 1)|) ≤ ∑' k : ℕ, |u k| := by
  have hsplit := hu.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  linarith [abs_nonneg (u 0)]

theorem barrierTrialT_abs_le (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {x : ℝ} (hx : |x| ≤ 1) :
    |barrierTrialT u x| ≤ ∑' k : ℕ, |u k| := by
  have hud : Summable (fun k : ℕ => |u (k + 1)|) :=
    (summable_nat_add_iff 1).mpr hu
  have hbound : ‖barrierTrialT u x‖ ≤ ∑' k : ℕ, |u (k + 1)| := by
    apply (barrierTrialT_summable u hu hx).hasSum.norm_le_of_bounded hud.hasSum
    intro k
    exact trial_scalar_norm_le (u (k + 1))
      ((Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) (Nat.succ_pos k)
      (Chebyshev.abs_eval_T_real_le_one ((k + 1 : ℕ) : ℤ) hx)
  simpa only [Real.norm_eq_abs] using hbound.trans (trial_abs_tail_le u hu)

theorem barrierTrialS_abs_le (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {x : ℝ} (hx : |x| ≤ 1) :
    |barrierTrialS u x| ≤ ∑' k : ℕ, |u k| := by
  have hud : Summable (fun k : ℕ => |u (k + 1)|) :=
    (summable_nat_add_iff 1).mpr hu
  have hbound : ‖barrierTrialS u x‖ ≤ ∑' k : ℕ, |u (k + 1)| := by
    apply (barrierTrialS_summable u hu hx).hasSum.norm_le_of_bounded hud.hasSum
    intro k
    apply trial_scalar_norm_le (u (k + 1)) (x ^ (k + 1)) (Nat.succ_pos k)
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) hx
  simpa only [Real.norm_eq_abs] using hbound.trans (trial_abs_tail_le u hu)

end

section

open Polynomial Set
open scoped BigOperators

theorem energy_sum_pairs_of_symmetric (m : ℕ) (f : Fin m → Fin m → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) =
      2 * (∑ i, ∑ j ∈ Finset.Ioi i, f i j) + (∑ i, f i i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have htail := ih (fun i j => f i.succ j.succ)
      (fun i j => hf i.succ j.succ)
    have hfull : (∑ i, ∑ j, f i j) =
        f 0 0 + (∑ j : Fin m, f 0 j.succ) + (∑ i : Fin m, f i.succ 0) +
          (∑ i : Fin m, ∑ j : Fin m, f i.succ j.succ) := by
      simp only [Fin.sum_univ_succ, Finset.sum_add_distrib]
      ring
    have hpair : (∑ i, ∑ j ∈ Finset.Ioi i, f i j) =
        (∑ j : Fin m, f 0 j.succ) +
          (∑ i : Fin m, ∑ j ∈ Finset.Ioi i, f i.succ j.succ) := by
      rw [Fin.sum_univ_succ, Fin.sum_Ioi_zero]
      simp only [Fin.sum_Ioi_succ]
    have hdiag : (∑ i, f i i) = f 0 0 + (∑ i : Fin m, f i.succ i.succ) := by
      rw [Fin.sum_univ_succ]
    have hcross : (∑ i : Fin m, f i.succ 0) = ∑ i : Fin m, f 0 i.succ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hf i.succ 0
    rw [hfull, hpair, hdiag, hcross, htail]
    ring

theorem energy_sum_pairs_one (m : ℕ) :
    (∑ i : Fin m, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) = (m.choose 2 : ℝ) := by
  have hh := energy_sum_pairs_of_symmetric m (fun _ _ => (1 : ℝ))
    (fun _ _ => rfl)
  have hfull : (∑ _i : Fin m, ∑ _j : Fin m, (1 : ℝ)) = (m : ℝ) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    ring
  have hdiag : (∑ _i : Fin m, (1 : ℝ)) = (m : ℝ) := by simp
  rw [hfull, hdiag] at hh
  rw [Nat.cast_choose_two]
  nlinarith only [hh]

theorem energy_sum_pairs_const (m : ℕ) (c : ℝ) :
    (∑ i : Fin m, ∑ _j ∈ Finset.Ioi i, c) = c * (m.choose 2 : ℝ) := by
  calc
    _ = (∑ i : Fin m, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) * c := by
      simp only [Finset.sum_mul, one_mul]
    _ = _ := by rw [energy_sum_pairs_one]; ring

theorem energy_sum_pairs_le_of_le_add (m : ℕ)
    (f g : Fin m → Fin m → ℝ) (c : ℝ)
    (hfg : ∀ i j, i < j → f i j ≤ g i j + c) :
    (∑ i, ∑ j ∈ Finset.Ioi i, f i j) ≤
      (∑ i, ∑ j ∈ Finset.Ioi i, g i j) + c * (m.choose 2 : ℝ) := by
  calc
    _ ≤ ∑ i, ∑ j ∈ Finset.Ioi i, (g i j + c) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hfg i j (Finset.mem_Ioi.mp hj)
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [energy_sum_pairs_const]

theorem realEnergyCosineKernel_symm {r u v : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1)
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    realEnergyCosineKernel r u v = realEnergyCosineKernel r v u := by
  have hswap : HasSum (fun k : ℕ =>
      2 * r ^ k * (Chebyshev.T ℝ (k : ℤ)).eval v *
        (Chebyshev.T ℝ (k : ℤ)).eval u / (k : ℝ))
      (-realEnergyCosineKernel r u v - Real.log 2) := by
    convert energy_hasSum_cosine_kernel hr hu hv using 1
    funext k
    ring
  have heq := hswap.unique (energy_hasSum_cosine_kernel hr hv hu)
  linarith

end

section

open Set
open scoped BigOperators

def realEnergyField (k x : ℝ) : ℝ :=
  (19 / 48 : ℝ) * Real.log |x| + (1 / 12 : ℝ) * Real.log (1 - x) -
    (k / 2 + 17 / 48) * Real.log (1 + x ^ 2)

def realEnergyColumnField (s : ℝ) : ℝ :=
  (7 / 48 : ℝ) * Real.log s + (1 / 12 : ℝ) * Real.log (1 - s)

def realEnergyCaseField (x : ℝ) : ℝ :=
  (1 / 6 : ℝ) - 2 * x ^ 2 / (1 + x ^ 2)

def realEnergyFiniteValue (N : ℕ) (k : ℝ) (x s : Fin (n N) → ℝ) : ℝ :=
  ((Cdegree N : ℝ) / (n N : ℝ) + (k - 2) / 2 - (k + 1) / (2 * (n N : ℝ))) *
      Real.log 2 +
    (∑ i : Fin (n N), (realEnergyField k (x i) +
      (k + 2) / (2 * (n N : ℝ)) * Real.log (1 + x i ^ 2))) / (n N : ℝ) +
    (∑ j : Fin (n N), realEnergyColumnField (s j)) / (n N : ℝ) +
    k * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / (n N : ℝ) ^ 2 +
    (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) / (n N : ℝ) ^ 2 +
    2 * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) / (n N : ℝ) ^ 2 -
    (∑ i : Fin (n N), ∑ j : Fin (n N), Real.log (1 - 2 * x i * s j + x i ^ 2)) /
      (n N : ℝ) ^ 2

theorem realEnergyMajorantOne_finite {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (realEnergyMajorantOne N x s) / (n N : ℝ) ^ 2 - Real.log 2 / 2 =
      realEnergyFiniteValue N 1 x s := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hC : 1 ≤ Cdegree N := Cdegree_pos hN
  rw [log_realEnergyMajorantOne hN x s hx hs hx0 hxi hsi]
  unfold realEnergyFiniteValue realEnergyField realEnergyColumnField
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Nat.cast_mul, Nat.cast_sub hC, Nat.cast_one]
  simp only [n, Cdegree, A, b, q, h, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hN0]
  ring

theorem realEnergyMajorantTwo_finite {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (realEnergyMajorantTwo N x s) / (n N : ℝ) ^ 2 - Real.log 2 / 2 =
      realEnergyFiniteValue N 2 x s := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hC : 1 ≤ Cdegree N := Cdegree_pos hN
  rw [log_realEnergyMajorantTwo hN x s hx hs hx0 hxi hsi]
  unfold realEnergyFiniteValue realEnergyField realEnergyColumnField
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Nat.cast_add, Nat.cast_mul, Nat.cast_sub hC, Nat.cast_one, Nat.cast_choose_two]
  simp only [n, Cdegree, A, b, q, h, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hN0]
  ring

end

section

open scoped BigOperators

theorem realEnergyCaseField_eq (x : ℝ) :
    realEnergyCaseField x = (1 - x ^ 2) / (1 + x ^ 2) - (5 / 6 : ℝ) := by
  unfold realEnergyCaseField
  have hd : 1 + x ^ 2 ≠ 0 := (realCoordinateInv_denominator_pos x).ne'
  field_simp [hd]
  ring

theorem realEnergyCaseField_average {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) :
    (∑ i : Fin (n N), realEnergyCaseField (x i)) / (n N : ℝ) =
      (∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) / (n N : ℝ) - 5 / 6 := by
  have hn0 : (n N : ℝ) ≠ 0 := by exact_mod_cast (show n N ≠ 0 by unfold n; omega)
  simp_rw [realEnergyCaseField_eq]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  field_simp [hn0]

theorem realEnergyCaseField_average_gt {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ)
    (hcase : ((n N - 1 - 2 * g N : ℕ) : ℝ) <
      ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) :
    -(1 / (n N : ℝ)) < (∑ i : Fin (n N), realEnergyCaseField (x i)) / (n N : ℝ) := by
  have hn : 1 ≤ n N := by unfold n; omega
  have hg : 2 * g N ≤ n N - 1 := by unfold n g; omega
  have hnpos : (0 : ℝ) < n N := by exact_mod_cast (show 0 < n N by omega)
  have hc : ((n N - 1 - 2 * g N : ℕ) : ℝ) = (5 / 6 : ℝ) * (n N : ℝ) - 1 := by
    rw [Nat.cast_sub hg, Nat.cast_sub hn, Nat.cast_one]
    simp only [n, g, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hd : ((n N - 1 - 2 * g N : ℕ) : ℝ) / (n N : ℝ) =
      5 / 6 - 1 / (n N : ℝ) := by
    rw [hc]
    field_simp [hnpos.ne']
  have he := div_lt_div_of_pos_right hcase hnpos
  rw [hd] at he
  rw [realEnergyCaseField_average hN x]
  linarith

theorem realEnergyCaseField_correction {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ)
    (hcase : ((n N - 1 - 2 * g N : ℕ) : ℝ) <
      ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2))
    (E lam : ℝ) (hlam : 0 ≤ lam) :
    E ≤ E + lam * ((∑ i : Fin (n N), realEnergyCaseField (x i)) / (n N : ℝ)) +
      lam / (n N : ℝ) := by
  have he := mul_le_mul_of_nonneg_left (realEnergyCaseField_average_gt hN x hcase).le hlam
  have hnorm : lam * (-(1 / (n N : ℝ))) = -(lam / (n N : ℝ)) := by ring
  rw [hnorm] at he
  linarith

end

open Set
open scoped BigOperators

def realEnergyOffDiagonalInteraction (N : ℕ) (k : ℝ) (x s : Fin (n N) → ℝ) : ℝ :=
  k * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / (n N : ℝ) ^ 2 +
  (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) / (n N : ℝ) ^ 2 +
  2 * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) / (n N : ℝ) ^ 2 -
  (∑ i : Fin (n N), ∑ j : Fin (n N), Real.log (1 - 2 * x i * s j + x i ^ 2)) /
    (n N : ℝ) ^ 2

theorem realEnergyOffDiagonalInteraction_le_damped {N : ℕ} (hN : 0 < N)
    {k e : ℝ} (hk : 0 ≤ k) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    realEnergyOffDiagonalInteraction N k x s ≤
      realEnergyDampedInteraction N k e x s -
      k / (2 * (n N : ℝ) ^ 2) *
        (∑ i : Fin (n N), realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x i)) -
      (∑ i : Fin (n N), Real.log (1 - (realEnergyRho e (x i) * x i) ^ 2)) /
        (2 * (n N : ℝ) ^ 2) -
      (∑ j : Fin (n N), realEnergyCosineKernel (realEnergySigma e (s j) ^ 2) (s j) (s j)) /
        (n N : ℝ) ^ 2 +
      (4 * k + 12) * e * ((n N).choose 2 : ℝ) / (n N : ℝ) ^ 2 + 6 * e := by
  have hn : (0 : ℝ) < n N := by
    have hnpos : 0 < n N := by unfold n; omega
    exact Nat.cast_pos.mpr hnpos
  let F : Fin (n N) → Fin (n N) → ℝ := fun i j =>
    realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)
  let G : Fin (n N) → Fin (n N) → ℝ := fun i j =>
    Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))
  let H : Fin (n N) → Fin (n N) → ℝ := fun i j =>
    realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)
  let Q : Fin (n N) → Fin (n N) → ℝ := fun i j =>
    Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
      (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)
  have hF := energy_sum_pairs_le_of_le_add (n N)
    (fun i j => Real.log |x j - x i|) F (4 * e) (fun i j hij => by
      dsimp [F]
      rw [abs_sub_comm (x j) (x i)]
      exact realEnergy_cosine_tau_le he ⟨(hx i).1.le, (hx i).2.le⟩
        ⟨(hx j).1.le, (hx j).2.le⟩ (fun h => (ne_of_lt hij) (hxi h)))
  have hG := energy_sum_pairs_le_of_le_add (n N)
    (fun i j => Real.log (1 - x i * x j)) G (4 * e) (fun i j _ => by
      have hc := realEnergy_power_kernel_le he (hx i) (hx j)
      dsimp [G]
      convert hc using 1; congr 2; ring)
  have hH := energy_sum_pairs_le_of_le_add (n N)
    (fun i j => Real.log |s j - s i|) H (4 * e) (fun i j hij => by
      dsimp [H]
      rw [abs_sub_comm (s j) (s i)]
      exact realEnergy_cosine_sigma_le he (hs i) (hs j)
        (fun h => (ne_of_lt hij) (hsi h)))
  have hQ :
      -(∑ i : Fin (n N), ∑ j : Fin (n N), Real.log (1 - 2 * x i * s j + x i ^ 2)) ≤
      -(∑ i : Fin (n N), ∑ j : Fin (n N), Q i j) + 6 * e * (n N : ℝ) ^ 2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun j _ => realEnergy_cross_kernel_le he (hx i) (hs j)))
    simpa only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Q, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using hh
  have ht := realEnergyTau_bounds he
  have htr : realEnergyTau e ^ 2 ∈ Ico (0 : ℝ) 1 := by
    refine ⟨sq_nonneg _, ?_⟩
    nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hFsym (i j : Fin (n N)) : F i j = F j i :=
    realEnergyCosineKernel_symm htr ⟨(hx i).1.le, (hx i).2.le⟩ ⟨(hx j).1.le, (hx j).2.le⟩
  have hGsym (i j : Fin (n N)) : G i j = G j i := by dsimp [G]; rw [mul_comm]
  have hHsym (i j : Fin (n N)) : H i j = H j i := by
    have hi := realEnergySigma_mem he (hs i)
    have hj := realEnergySigma_mem he (hs j)
    have hr : realEnergySigma e (s i) * realEnergySigma e (s j) ∈ Ico (0 : ℝ) 1 :=
      ⟨mul_nonneg hi.1.le hj.1.le, (realEnergySigma_mul_bounds he (hs i) (hs j)).2⟩
    dsimp [H]
    rw [realEnergyCosineKernel_symm hr
      ⟨by linarith [(hs i).1], (hs i).2.le⟩ ⟨by linarith [(hs j).1], (hs j).2.le⟩]
    rw [mul_comm]
  have hpF : (∑ i, ∑ j ∈ Finset.Ioi i, F i j) =
      ((∑ i, ∑ j, F i j) - ∑ i, F i i) / 2 := by
    linarith [energy_sum_pairs_of_symmetric (n N) F hFsym]
  have hpG : (∑ i, ∑ j ∈ Finset.Ioi i, G i j) =
      ((∑ i, ∑ j, G i j) - ∑ i, G i i) / 2 := by
    linarith [energy_sum_pairs_of_symmetric (n N) G hGsym]
  have hpH : (∑ i, ∑ j ∈ Finset.Ioi i, H i j) =
      ((∑ i, ∑ j, H i j) - ∑ i, H i i) / 2 := by
    linarith [energy_sum_pairs_of_symmetric (n N) H hHsym]
  have hh := add_le_add
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hF hk) hG)
      (mul_le_mul_of_nonneg_left hH (by norm_num : (0 : ℝ) ≤ 2))) hQ
  have hd := div_le_div_of_nonneg_right hh (sq_nonneg (n N : ℝ))
  calc
    realEnergyOffDiagonalInteraction N k x s =
        (k * (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) +
          (∑ i, ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) +
          2 * (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) +
          -(∑ i, ∑ j, Real.log (1 - 2 * x i * s j + x i ^ 2))) / (n N : ℝ) ^ 2 := by
      unfold realEnergyOffDiagonalInteraction
      ring
    _ ≤ _ := hd
    _ = _ := by
      rw [hpF, hpG, hpH]
      dsimp [F, G, H, Q, realEnergyDampedInteraction]
      simp only [pow_two]
      field_simp [hn.ne']; ring

def realEnergyRegularizationError (N : ℕ) (k e : ℝ) : ℝ :=
  2 * Real.log 2 / (n N : ℝ) +
    k * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / (2 * (n N : ℝ)) +
    (Real.log 2 - Real.log e) / (2 * (n N : ℝ)) +
    (Real.log 2 - 2 * Real.log e) / (n N : ℝ) +
    (4 * k + 12) * e * ((n N).choose 2 : ℝ) / (n N : ℝ) ^ 2 + 6 * e

theorem realEnergyFiniteValue_le_regularized {N : ℕ} (hN : 0 < N)
    {k e : ℝ} (hk : k = 1 ∨ k = 2) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    realEnergyFiniteValue N k x s ≤
      ((Cdegree N : ℝ) / (n N : ℝ) + (k - 2) / 2 - (k + 1) / (2 * (n N : ℝ))) *
        Real.log 2 +
      (∑ i : Fin (n N), (realEnergyField k (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) +
      (∑ j : Fin (n N), (realEnergyColumnField (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) +
      realEnergyDampedInteraction N k e x s + realEnergyRegularizationError N k e := by
  have hn : (n N : ℝ) ≠ 0 := by
    have hnpos : 0 < n N := by unfold n; omega
    exact (Nat.cast_pos.mpr hnpos).ne'
  have hk0 : 0 ≤ k := by
    rcases hk with rfl | rfl <;> norm_num
  have hcorrection :
      (∑ i : Fin (n N), ((k + 2) / (2 * (n N : ℝ)) *
        Real.log (1 + x i ^ 2))) / (n N : ℝ) ≤ 2 * Real.log 2 / (n N : ℝ) := by
    convert (realEnergyFiniteCorrection_bounds hN k hk x hx).2 using 1; ring
  have hinteraction := realEnergyOffDiagonalInteraction_le_damped hN hk0 he hx hs hxi hsi
  have htau := realEnergy_tau_diagonal_sum hN he hk0 hx
  have hpower := realEnergy_power_diagonal_sum hN he hx
  have hsigma := realEnergy_sigma_diagonal_sum hN he hs

  simp only [mul_pow] at hinteraction
  simp only [neg_mul] at htau
  simp only [neg_div] at hpower hsigma
  have hsplit : realEnergyFiniteValue N k x s =
      ((Cdegree N : ℝ) / (n N : ℝ) + (k - 2) / 2 - (k + 1) / (2 * (n N : ℝ))) *
        Real.log 2 +
      (∑ i : Fin (n N), realEnergyField k (x i)) / (n N : ℝ) +
      (∑ j : Fin (n N), realEnergyColumnField (s j)) / (n N : ℝ) +
      (∑ i : Fin (n N), ((k + 2) / (2 * (n N : ℝ)) *
        Real.log (1 + x i ^ 2))) / (n N : ℝ) +
      realEnergyOffDiagonalInteraction N k x s := by
    unfold realEnergyFiniteValue realEnergyOffDiagonalInteraction
    rw [Finset.sum_add_distrib]
    ring
  have hrow :
      (∑ i : Fin (n N), (realEnergyField k (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) =
      (∑ i : Fin (n N), realEnergyField k (x i)) / (n N : ℝ) -
        (∑ i : Fin (n N), Real.log (1 - x i)) / (2 * (n N : ℝ) ^ 2) := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div]
    field_simp [hn]
  have hcolumn :
      (∑ j : Fin (n N), (realEnergyColumnField (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) =
      (∑ j : Fin (n N), realEnergyColumnField (s j)) / (n N : ℝ) -
        (∑ j : Fin (n N), Real.log (1 - s j)) / (n N : ℝ) ^ 2 := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div]
    field_simp [hn]
  rw [hsplit, hrow, hcolumn]
  unfold realEnergyRegularizationError
  linarith only [hcorrection, hinteraction, htau, hpower, hsigma]

def realEnergyRowTrialField (k lam : ℝ) (p v : ℕ → ℝ) (x : ℝ) : ℝ :=
  realEnergyField k x + lam * realEnergyCaseField x -
    2 * k * barrierTrialT p x - barrierTrialS v x

def realEnergyColumnTrialField (v : ℕ → ℝ) (s : ℝ) : ℝ :=
  realEnergyColumnField s + 2 * barrierTrialT v s

theorem realEnergyFiniteValue_le_trialFields {N : ℕ} (hN : 0 < N)
    {k e lam : ℝ} (hk : k = 1 ∨ k = 2) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hlam : 0 ≤ lam) {x s : Fin (n N) → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hcase : lam = 0 ∨ (((n N - 1 - 2 * g N : ℕ) : ℝ) <
      ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)))
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|)) :
    realEnergyFiniteValue N k x s ≤
      (-(11 / 16 : ℝ) - (k + 1) / (2 * (n N : ℝ))) * Real.log 2 +
      k * barrierTrialNormSq p + barrierTrialNormSq v / 2 +
      (∑ i : Fin (n N), (realEnergyRowTrialField k lam p v (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) +
      (∑ j : Fin (n N), (realEnergyColumnTrialField v (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) +
      realEnergyRegularizationError N k e +
      2 * k * e * (∑' j : ℕ, |p j|) + 4 * e * (∑' j : ℕ, |v j|) + lam / (n N : ℝ) := by
  have hk0 : 0 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  have hfinite := realEnergyFiniteValue_le_regularized hN hk he hx hs hxi hsi
  have hdual := realEnergyDampedInteraction_le_canonicalTrials hN hk0 he hx hs p v hp hv
  have hcaseAdd : 0 ≤ lam * ((∑ i : Fin (n N), realEnergyCaseField (x i)) / (n N : ℝ)) +
      lam / (n N : ℝ) := by
    rcases hcase with hlam0 | hfail
    · simp [hlam0]
    · simpa only [zero_add] using realEnergyCaseField_correction hN x hfail 0 lam hlam
  have hrow :
      (∑ i : Fin (n N), (realEnergyRowTrialField k lam p v (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) =
      (∑ i : Fin (n N), (realEnergyField k (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) +
      (∑ i : Fin (n N), (-2 * k * barrierTrialT p (x i) - barrierTrialS v (x i))) / (n N : ℝ) +
      lam * ((∑ i : Fin (n N), realEnergyCaseField (x i)) / (n N : ℝ)) := by
    unfold realEnergyRowTrialField
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hcolumn :
      (∑ j : Fin (n N), (realEnergyColumnTrialField v (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) =
      (∑ j : Fin (n N), (realEnergyColumnField (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) +
      (∑ j : Fin (n N), 2 * barrierTrialT v (s j)) / (n N : ℝ) := by
    unfold realEnergyColumnTrialField
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hconstant := congrArg (fun z : ℝ => z * Real.log 2) (energy_constant_after_squares hN k)
  norm_num only at hconstant
  rw [hrow, hcolumn]
  simp only [div_eq_mul_inv, mul_inv_rev] at hfinite hdual hcaseAdd hconstant ⊢
  nlinarith only [hfinite, hdual, hcaseAdd, hconstant]

theorem realEnergyRowTrialField_residual_le {k lam x : ℝ}
    (hk : 0 ≤ k) (hlam : 0 ≤ lam) (hx : |x| ≤ 1)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|)) :
    realEnergyRowTrialField k lam p v x - (1 / 12 : ℝ) * Real.log (1 - x) ≤
      lam / 6 + 2 * k * (∑' j : ℕ, |p j|) + (∑' j : ℕ, |v j|) := by
  have habs := Real.log_nonpos (abs_nonneg x) hx
  have hquad := Real.log_nonneg (show (1 : ℝ) ≤ 1 + x ^ 2 by nlinarith [sq_nonneg x])
  have hD : realEnergyCaseField x ≤ (1 / 6 : ℝ) := by
    unfold realEnergyCaseField
    have hh : 0 ≤ 2 * x ^ 2 / (1 + x ^ 2) := by positivity
    linarith
  have hlamD := mul_le_mul_of_nonneg_left hD hlam
  have hT := mul_le_mul_of_nonneg_left (abs_le.mp (barrierTrialT_abs_le p hp hx)).1
    (show 0 ≤ 2 * k by positivity)
  have hS := (abs_le.mp (barrierTrialS_abs_le v hv hx)).1
  have hlog := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 19 / 48) habs
  have hlogq := mul_nonneg (show 0 ≤ k / 2 + 17 / 48 by positivity) hquad
  unfold realEnergyRowTrialField realEnergyField
  nlinarith only [hlamD, hT, hS, hlog, hlogq]

theorem realEnergyColumnTrialField_residual_le {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (v : ℕ → ℝ) (hv : Summable (fun j => |v j|)) :
    realEnergyColumnTrialField v s - (1 / 12 : ℝ) * Real.log (1 - s) ≤
      2 * (∑' j : ℕ, |v j|) := by
  have hlog := Real.log_nonpos hs.1.le hs.2.le
  have hsabs : |s| ≤ 1 := by rw [abs_of_pos hs.1]; exact hs.2.le
  have hT := (abs_le.mp (barrierTrialT_abs_le v hv hsabs)).2
  unfold realEnergyColumnTrialField realEnergyColumnField
  linarith

theorem energy_endpoint_convex_bound {G L B H d : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hG : G ≤ B) (hH : G - L / 12 ≤ H) :
    G - d * L / 12 ≤ B + d * (H - B) := by
  have hfirst := mul_le_mul_of_nonneg_left hG (sub_nonneg.mpr hd1)
  have hsecond := mul_le_mul_of_nonneg_left hH hd0
  nlinarith only [hfirst, hsecond]

theorem realEnergyRowTrialField_weaken_le {N : ℕ} (hN : 0 < N)
    {k lam x B : ℝ} (hk : 0 ≤ k) (hlam : 0 ≤ lam) (hx : |x| ≤ 1)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hB : realEnergyRowTrialField k lam p v x ≤ B) :
    realEnergyRowTrialField k lam p v x - Real.log (1 - x) / (2 * (n N : ℝ)) ≤
      B + 6 * (lam / 6 + 2 * k * (∑' j : ℕ, |p j|) + (∑' j : ℕ, |v j|) - B) / (n N : ℝ) := by
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hn6 : (6 : ℝ) ≤ n N := by
    exact_mod_cast (show 6 ≤ n N by unfold n; omega)
  have hd0 : (0 : ℝ) ≤ 6 / (n N : ℝ) := by positivity
  have hd1 : (6 : ℝ) / (n N : ℝ) ≤ 1 := (div_le_iff₀ hn).mpr (by simpa using hn6)
  have hr := realEnergyRowTrialField_residual_le hk hlam hx p v hp hv
  have hres : realEnergyRowTrialField k lam p v x - Real.log (1 - x) / 12 ≤
      lam / 6 + 2 * k * (∑' j : ℕ, |p j|) + (∑' j : ℕ, |v j|) := by
    convert hr using 1; ring
  convert energy_endpoint_convex_bound hd0 hd1 hB hres using 1 <;> ring

theorem realEnergyColumnTrialField_weaken_le {N : ℕ} (hN : 0 < N)
    {s B : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (v : ℕ → ℝ) (hv : Summable (fun j => |v j|))
    (hB : realEnergyColumnTrialField v s ≤ B) :
    realEnergyColumnTrialField v s - Real.log (1 - s) / (n N : ℝ) ≤
      B + 12 * (2 * (∑' j : ℕ, |v j|) - B) / (n N : ℝ) := by
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hn12 : (12 : ℝ) ≤ n N := by
    exact_mod_cast (show 12 ≤ n N by unfold n; omega)
  have hd0 : (0 : ℝ) ≤ 12 / (n N : ℝ) := by positivity
  have hd1 : (12 : ℝ) / (n N : ℝ) ≤ 1 := (div_le_iff₀ hn).mpr (by simpa using hn12)
  have hr := realEnergyColumnTrialField_residual_le hs v hv
  have hres : realEnergyColumnTrialField v s - Real.log (1 - s) / 12 ≤
      2 * (∑' j : ℕ, |v j|) := by convert hr using 1; ring
  convert energy_endpoint_convex_bound hd0 hd1 hB hres using 1 <;> ring

def realEnergyDualConstant (k : ℝ) (p v : ℕ → ℝ) (Bx Bs : ℝ) : ℝ :=
  -(11 / 16 : ℝ) * Real.log 2 + k * barrierTrialNormSq p + barrierTrialNormSq v / 2 + Bx + Bs

def realEnergyDualDampingCoefficient (k : ℝ) (p v : ℕ → ℝ) : ℝ :=
  2 * k + 12 + 2 * k * (∑' j : ℕ, |p j|) + 4 * (∑' j : ℕ, |v j|)

def realEnergyDualFiniteCoefficient (k e lam : ℝ) (p v : ℕ → ℝ) (Bx Bs : ℝ) : ℝ :=
  2 * Real.log 2 + k / 2 * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) +
    (Real.log 2 - Real.log e) / 2 + (Real.log 2 - 2 * Real.log e) + lam +
    6 * (lam / 6 + 2 * k * (∑' j : ℕ, |p j|) + (∑' j : ℕ, |v j|) - Bx) +
    12 * (2 * (∑' j : ℕ, |v j|) - Bs)

theorem realEnergyRegularizationError_le {N : ℕ} (hN : 0 < N)
    {k e : ℝ} (hk : 0 ≤ k) (he : 0 ≤ e) :
    realEnergyRegularizationError N k e ≤
      (2 * Real.log 2 + k / 2 * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) +
        (Real.log 2 - Real.log e) / 2 + (Real.log 2 - 2 * Real.log e)) / (n N : ℝ) +
      (2 * k + 12) * e := by
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hc : ((n N).choose 2 : ℝ) ≤ (n N : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith only [hn.le]
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ (4 * k + 12) * e by positivity)
  have hh : (4 * k + 12) * e * ((n N).choose 2 : ℝ) / (n N : ℝ) ^ 2 ≤
      (2 * k + 6) * e := by
    apply (div_le_div_of_nonneg_right hm (sq_nonneg (n N : ℝ))).trans_eq
    field_simp [hn.ne']; ring
  unfold realEnergyRegularizationError
  simp only [div_eq_mul_inv, mul_inv_rev] at hh ⊢
  nlinarith only [hh]

theorem realEnergyFiniteValue_le_uniformDual {N : ℕ} (hN : 0 < N)
    {k e lam Bx Bs : ℝ} (hk : k = 1 ∨ k = 2) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hlam : 0 ≤ lam) {x s : Fin (n N) → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hcase : lam = 0 ∨ (((n N - 1 - 2 * g N : ℕ) : ℝ) <
      ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)))
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField k lam p v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs) :
    realEnergyFiniteValue N k x s ≤ realEnergyDualConstant k p v Bx Bs +
      e * realEnergyDualDampingCoefficient k p v +
      realEnergyDualFiniteCoefficient k e lam p v Bx Bs / (n N : ℝ) := by
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hk0 : 0 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  have hrow :
      (∑ i : Fin (n N), (realEnergyRowTrialField k lam p v (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) ≤
      Bx + 6 * (lam / 6 + 2 * k * (∑' j : ℕ, |p j|) + (∑' j : ℕ, |v j|) - Bx) / (n N : ℝ) := by
    apply (div_le_iff₀ hn).mpr
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      realEnergyRowTrialField_weaken_le hN hk0 hlam
        (abs_le.mpr ⟨(hx i).1.le, (hx i).2.le⟩) p v hp hv
        (hBx (x i) ⟨(hx i).1.le, (hx i).2⟩ (hx0 i)))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using hh
  have hcolumn :
      (∑ j : Fin (n N), (realEnergyColumnTrialField v (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) ≤
      Bs + 12 * (2 * (∑' j : ℕ, |v j|) - Bs) / (n N : ℝ) := by
    apply (div_le_iff₀ hn).mpr
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      realEnergyColumnTrialField_weaken_le hN (hs j) v hv (hBs (s j) (hs j)))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using hh
  have hfinite := realEnergyFiniteValue_le_trialFields hN hk he hlam hx hs hxi hsi hcase p v hp hv
  have herror := realEnergyRegularizationError_le hN hk0 he.1.le
  have hconst : (-(11 / 16 : ℝ) - (k + 1) / (2 * (n N : ℝ))) * Real.log 2 ≤
      -(11 / 16 : ℝ) * Real.log 2 := by
    have hh : 0 ≤ ((k + 1) / (2 * (n N : ℝ))) * Real.log 2 :=
      mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    nlinarith only [hh]
  unfold realEnergyDualConstant realEnergyDualDampingCoefficient realEnergyDualFiniteCoefficient
  simp only [div_eq_mul_inv, mul_inv_rev] at hrow hcolumn hfinite herror hconst ⊢
  nlinarith only [hrow, hcolumn, hfinite, herror, hconst]

theorem realEnergyDualDampingCoefficient_nonneg {k : ℝ} (hk : 0 ≤ k)
    (p v : ℕ → ℝ) : 0 ≤ realEnergyDualDampingCoefficient k p v := by
  have hp : 0 ≤ ∑' j : ℕ, |p j| := tsum_nonneg (fun _ => abs_nonneg _)
  have hv : 0 ≤ ∑' j : ℕ, |v j| := tsum_nonneg (fun _ => abs_nonneg _)
  unfold realEnergyDualDampingCoefficient
  positivity

theorem realEnergy_uniform_dual_eventually
    {k lam Bx Bs : ℝ} (hk : k = 1 ∨ k = 2) (hlam : 0 ≤ lam)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField k lam p v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (lam = 0 ∨ (((n N - 1 - 2 * g N : ℕ) : ℝ) <
        ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2))) →
      realEnergyFiniteValue N k x s ≤ realEnergyDualConstant k p v Bx Bs + d := by
  have hk0 : 0 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  let D : ℝ := realEnergyDualDampingCoefficient k p v
  have hD : 0 ≤ D := realEnergyDualDampingCoefficient_nonneg hk0 p v
  let e : ℝ := min (1 / 16) (d / (2 * (D + 1)))
  have he0 : 0 < e := by
    apply lt_min (by norm_num)
    exact div_pos hd (by positivity)
  have he8 : e < (1 / 8 : ℝ) := by
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have he : e ∈ Ioo (0 : ℝ) (1 / 8) := ⟨he0, he8⟩
  have heD : e * D < d / 2 := by
    have heSmall : e ≤ d / (2 * (D + 1)) := min_le_right _ _
    have hprod := (le_div_iff₀ (show 0 < 2 * (D + 1) by positivity)).mp heSmall
    nlinarith only [hprod, he0]
  let C : ℝ := realEnergyDualFiniteCoefficient k e lam p v Bx Bs
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * |C| / d)
  refine ⟨M + 1, ?_⟩
  intro N hNlarge x s hx hs hx0 hxi hsi hcase
  have hN : 0 < N := by omega
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hMN : M ≤ n N := by unfold n; omega
  have hbig : 2 * |C| / d < (n N : ℝ) :=
    hM.trans_le (Nat.cast_le.mpr hMN)
  have hCabs : |C| / (n N : ℝ) < d / 2 := by
    apply (div_lt_iff₀ hn).mpr
    have hprod := (div_lt_iff₀ hd).mp hbig
    nlinarith only [hprod]
  have hC : C / (n N : ℝ) < d / 2 :=
    (div_le_div_of_nonneg_right (le_abs_self C) hn.le).trans_lt hCabs
  have hfinite := realEnergyFiniteValue_le_uniformDual hN hk he hlam hx hs hx0 hxi hsi
    hcase p v hp hv hBx hBs
  change realEnergyFiniteValue N k x s ≤ realEnergyDualConstant k p v Bx Bs +
    e * D + C / (n N : ℝ) at hfinite
  linarith only [hfinite, heD, hC]

theorem realEnergyMajorantOne_uniform_dual {lam Bx Bs : ℝ} (hlam : 0 ≤ lam)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 1 lam p v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (((n N - 1 - 2 * g N : ℕ) : ℝ) <
        ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) →
      Real.log (realEnergyMajorantOne N x s) / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        realEnergyDualConstant 1 p v Bx Bs + d := by
  obtain ⟨M, hM⟩ := realEnergy_uniform_dual_eventually (Or.inl rfl) hlam p v hp hv hBx hBs hd
  refine ⟨M + 1, ?_⟩
  intro N hNlarge x s hx hs hx0 hxi hsi hcase
  have hN : 0 < N := by omega
  rw [realEnergyMajorantOne_finite hN x s hx hs hx0 hxi hsi]
  exact hM N (by omega) x s hx hs hx0 hxi hsi (Or.inr hcase)

theorem realEnergyMajorantTwo_uniform_dual {Bx Bs : ℝ}
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 2 0 p v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      Real.log (realEnergyMajorantTwo N x s) / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        realEnergyDualConstant 2 p v Bx Bs + d := by
  obtain ⟨M, hM⟩ := realEnergy_uniform_dual_eventually (Or.inr rfl) (le_refl (0 : ℝ))
    p v hp hv hBx hBs hd
  refine ⟨M + 1, ?_⟩
  intro N hNlarge x s hx hs hx0 hxi hsi
  have hN : 0 < N := by omega
  rw [realEnergyMajorantTwo_finite hN x s hx hs hx0 hxi hsi]
  exact hM N (by omega) x s hx hs hx0 hxi hsi (Or.inl rfl)

open Set
open scoped BigOperators

def realEnergyRowTrialSup (k lam : ℝ) (p v : ℕ → ℝ) : ℝ :=
  sSup (realEnergyRowTrialField k lam p v '' {x : ℝ | x ∈ Ico (-1 : ℝ) 1 ∧ x ≠ 0})

def realEnergyColumnTrialSup (v : ℕ → ℝ) : ℝ :=
  sSup (realEnergyColumnTrialField v '' Ioo (0 : ℝ) 1)

theorem realEnergyRowTrialField_image_bddAbove {k lam : ℝ}
    (hk : 0 ≤ k) (hlam : 0 ≤ lam)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|)) :
    BddAbove (realEnergyRowTrialField k lam p v '' {x : ℝ | x ∈ Ico (-1 : ℝ) 1 ∧ x ≠ 0}) := by
  refine ⟨lam / 6 + 2 * k * (∑' j : ℕ, |p j|) + (∑' j : ℕ, |v j|) + Real.log 2 / 12, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have habs : |x| ≤ 1 := abs_le.mpr ⟨hx.1.1, hx.1.2.le⟩
  have hres := realEnergyRowTrialField_residual_le hk hlam habs p v hp hv
  have hlog : Real.log (1 - x) ≤ Real.log 2 :=
    Real.log_le_log (sub_pos.mpr hx.1.2) (by linarith [hx.1.1])
  linarith

theorem realEnergyColumnTrialField_image_bddAbove
    (v : ℕ → ℝ) (hv : Summable (fun j => |v j|)) :
    BddAbove (realEnergyColumnTrialField v '' Ioo (0 : ℝ) 1) := by
  refine ⟨2 * (∑' j : ℕ, |v j|), ?_⟩
  rintro y ⟨s, hs, rfl⟩
  have hres := realEnergyColumnTrialField_residual_le hs v hv
  have hlog : Real.log (1 - s) ≤ 0 :=
    Real.log_nonpos (sub_pos.mpr hs.2).le (by linarith [hs.1])
  linarith

theorem realEnergyRowTrialField_image_nonempty (k lam : ℝ) (p v : ℕ → ℝ) :
    (realEnergyRowTrialField k lam p v '' {x : ℝ | x ∈ Ico (-1 : ℝ) 1 ∧ x ≠ 0}).Nonempty := by
  refine ⟨realEnergyRowTrialField k lam p v (-1 / 2), -1 / 2, ?_, rfl⟩
  norm_num

theorem realEnergyColumnTrialField_image_nonempty (v : ℕ → ℝ) :
    (realEnergyColumnTrialField v '' Ioo (0 : ℝ) 1).Nonempty := by
  refine ⟨realEnergyColumnTrialField v (1 / 2), 1 / 2, ?_, rfl⟩
  norm_num

theorem realEnergyRowTrialField_le_sup {k lam : ℝ}
    (hk : 0 ≤ k) (hlam : 0 ≤ lam)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    {x : ℝ} (hx : x ∈ Ico (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    realEnergyRowTrialField k lam p v x ≤ realEnergyRowTrialSup k lam p v := by
  exact le_csSup (realEnergyRowTrialField_image_bddAbove hk hlam p v hp hv) ⟨x, ⟨hx, hx0⟩, rfl⟩

theorem realEnergyColumnTrialField_le_sup
    (v : ℕ → ℝ) (hv : Summable (fun j => |v j|)) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    realEnergyColumnTrialField v s ≤ realEnergyColumnTrialSup v := by
  exact le_csSup (realEnergyColumnTrialField_image_bddAbove v hv) ⟨s, hs, rfl⟩

theorem realEnergy_uniform_sup_dual_eventually
    {k lam : ℝ} (hk : k = 1 ∨ k = 2) (hlam : 0 ≤ lam)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (lam = 0 ∨ (((n N - 1 - 2 * g N : ℕ) : ℝ) <
        ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2))) →
      realEnergyFiniteValue N k x s ≤
        realEnergyDualConstant k p v (realEnergyRowTrialSup k lam p v) (realEnergyColumnTrialSup v) + d := by
  have hk0 : 0 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  exact realEnergy_uniform_dual_eventually hk hlam p v hp hv
    (fun z hz hz0 => realEnergyRowTrialField_le_sup hk0 hlam p v hp hv hz hz0)
    (fun z hz => realEnergyColumnTrialField_le_sup v hv hz) hd

end InternalCatalan

end

end OAI
