import OAI.NumberTheory.Catalan.Analysis.RealEnergyKernelSeries
import OAI.NumberTheory.Catalan.Estimates.RealEnergyTrialDamping
import OAI.NumberTheory.Catalan.Estimates.TwoAdicQuadratic

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial Set
open scoped BigOperators

def realEnergyCosineMoment (N : ℕ) (e : ℝ) (x : Fin (n N) → ℝ) (k : ℕ) : ℝ :=
  (∑ i, realEnergyTau e ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (x i)) / (n N : ℝ)

def realEnergyPowerMoment (N : ℕ) (e : ℝ) (x : Fin (n N) → ℝ) (k : ℕ) : ℝ :=
  (∑ i, realEnergyRho e (x i) ^ k * x i ^ k) / (n N : ℝ)

def realEnergyColumnMoment (N : ℕ) (e : ℝ) (s : Fin (n N) → ℝ) (k : ℕ) : ℝ :=
  (∑ j, realEnergySigma e (s j) ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (s j)) /
    (n N : ℝ)

theorem energy_sum_sum_mul_div {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) (c d : ℝ) :
    (∑ i, ∑ j, c * a i * b j / d) = c * (∑ i, a i) * (∑ j, b j) / d := by
  calc
    _ = ∑ i, (c * a i) * (∑ j, b j) / d := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_div, ← Finset.mul_sum]
    _ = (∑ i, c * a i) * (∑ j, b j) / d := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
    _ = _ := by rw [← Finset.mul_sum]

theorem energy_cosineMoment_square_div_eq (N : ℕ) (e : ℝ)
    (x : Fin (n N) → ℝ) (k : ℕ) :
    realEnergyCosineMoment N e x k ^ 2 / (k : ℝ) =
      (1 / (2 * (n N : ℝ) ^ 2)) *
        (∑ i : Fin (n N), ∑ j : Fin (n N),
          2 * (realEnergyTau e ^ 2) ^ k *
            (Chebyshev.T ℝ (k : ℤ)).eval (x i) *
            (Chebyshev.T ℝ (k : ℤ)).eval (x j) / (k : ℝ)) := by
  unfold realEnergyCosineMoment
  rw [← Finset.mul_sum, energy_sum_sum_mul_div]
  simp only [pow_two, mul_pow, div_eq_mul_inv, mul_inv_rev]
  ring

theorem energy_hasSum_first_square {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => realEnergyCosineMoment N e x k ^ 2 / (k : ℝ))
      (-((∑ i : Fin (n N), ∑ j : Fin (n N),
            realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) /
          (n N : ℝ) ^ 2 + Real.log 2) / 2) := by
  have ht := realEnergyTau_bounds he
  have hr : realEnergyTau e ^ 2 ∈ Ico (0 : ℝ) 1 := by
    refine ⟨sq_nonneg _, ?_⟩
    have hm := mul_lt_mul_of_pos_left ht.2 ht.1
    nlinarith [ht.2]
  have hn : (n N : ℝ) ≠ 0 := by
    have hnpos : 0 < n N := by unfold n; omega
    exact (Nat.cast_pos.mpr hnpos).ne'
  have hseries :
      HasSum (fun k : ℕ => ∑ i : Fin (n N), ∑ j : Fin (n N),
          2 * (realEnergyTau e ^ 2) ^ k *
            (Chebyshev.T ℝ (k : ℤ)).eval (x i) *
            (Chebyshev.T ℝ (k : ℤ)).eval (x j) / (k : ℝ))
        (∑ i : Fin (n N), ∑ j : Fin (n N),
          (-realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j) -
            Real.log 2)) := by
    apply hasSum_sum
    intro i hi
    apply hasSum_sum
    intro j hj
    exact energy_hasSum_cosine_kernel hr
      ⟨(hx i).1.le, (hx i).2.le⟩ ⟨(hx j).1.le, (hx j).2.le⟩
  convert hseries.mul_left (1 / (2 * (n N : ℝ) ^ 2)) using 1
  · funext k
    exact energy_cosineMoment_square_div_eq N e x k
  · simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn]
    ring

theorem energy_summable_abs_first_square {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    Summable (fun k : ℕ => |realEnergyCosineMoment N e x k ^ 2 / (k : ℝ)|) :=
  (energy_hasSum_first_square hN he hx).summable.abs

end

section

open Set
open scoped BigOperators

theorem energy_abs_average_le_one {m : ℕ} (hm : 0 < m)
    (a : Fin m → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    |(∑ i, a i) / (m : ℝ)| ≤ 1 := by
  have hmp : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rw [abs_div, abs_of_pos hmp]
  apply (div_le_iff₀ hmp).mpr
  calc
    |∑ i, a i| ≤ ∑ i, |a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, (1 : ℝ) := Finset.sum_le_sum (fun i _ => ha i)
    _ = 1 * (m : ℝ) := by simp

theorem energy_cosineMoment_abs_le_one {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (k : ℕ) :
    |realEnergyCosineMoment N e x k| ≤ 1 := by
  have hn : 0 < n N := by unfold n; omega
  apply energy_abs_average_le_one hn
  intro i
  have ht := realEnergyTau_bounds he
  rw [abs_mul, abs_pow, abs_of_pos ht.1]
  exact (mul_le_mul (pow_le_one₀ ht.1.le ht.2.le)
    (energy_chebyshev_abs_le_one k ⟨(hx i).1.le, (hx i).2.le⟩)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem energy_powerMoment_abs_le_one {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (k : ℕ) :
    |realEnergyPowerMoment N e x k| ≤ 1 := by
  have hn : 0 < n N := by unfold n; omega
  apply energy_abs_average_le_one hn
  intro i
  have hr := realEnergyRho_mem he (hx i)
  rw [abs_mul, abs_pow, abs_pow, abs_of_pos hr.1]
  exact (mul_le_mul (pow_le_one₀ hr.1.le hr.2.le)
    (pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨(hx i).1.le, (hx i).2.le⟩))
    (pow_nonneg (abs_nonneg _) _) (by norm_num)).trans_eq (one_mul _)

theorem energy_columnMoment_abs_le_one {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {s : Fin (n N) → ℝ} (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    |realEnergyColumnMoment N e s k| ≤ 1 := by
  have hn : 0 < n N := by unfold n; omega
  apply energy_abs_average_le_one hn
  intro j
  have hr := realEnergySigma_mem he (hs j)
  rw [abs_mul, abs_pow, abs_of_pos hr.1]
  exact (mul_le_mul (pow_le_one₀ hr.1.le hr.2.le)
    (energy_chebyshev_abs_le_one k ⟨by linarith [(hs j).1], (hs j).2.le⟩)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem energy_secondMoment_abs_le_three {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    |realEnergyPowerMoment N e x k - 2 * realEnergyColumnMoment N e s k| ≤ 3 := by
  have hb := energy_powerMoment_abs_le_one hN he hx k
  have hc := energy_columnMoment_abs_le_one hN he hs k
  calc
    _ ≤ |realEnergyPowerMoment N e x k| + |2 * realEnergyColumnMoment N e s k| :=
      abs_sub _ _
    _ = |realEnergyPowerMoment N e x k| + 2 * |realEnergyColumnMoment N e s k| := by
      rw [abs_mul]; norm_num
    _ ≤ 3 := by linarith

theorem energy_trial_norm_summable (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    Summable (fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
  have ht : Summable (fun k : ℕ => |u (k + 1)|) := (summable_nat_add_iff 1).mpr hu
  apply (ht.mul_left (∑' k, |u k|)).of_norm_bounded
  intro k
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk
  have hb : |u (k + 1)| ≤ ∑' j, |u j| := hu.le_tsum (k + 1) (fun j _ => abs_nonneg _)
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hkp]
  calc
    _ ≤ |u (k + 1)| ^ 2 := div_le_self (sq_nonneg _) hk
    _ ≤ (∑' j, |u j|) * |u (k + 1)| := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hb (abs_nonneg (u (k + 1)))

theorem energy_trial_product_summable (u a : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ k, |a k| ≤ K) :
    Summable (fun k : ℕ => u (k + 1) * a (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  have ht : Summable (fun k : ℕ => |u (k + 1)|) := (summable_nat_add_iff 1).mpr hu
  apply (ht.mul_left K).of_norm_bounded
  intro k
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk
  rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hkp]
  calc
    _ ≤ |u (k + 1)| * K / ((k + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (ha _) (abs_nonneg _)) hkp.le
    _ ≤ |u (k + 1)| * K := div_le_self (mul_nonneg (abs_nonneg _) hK) hk
    _ = K * |u (k + 1)| := mul_comm _ _

end

section

open Polynomial Set
open scoped BigOperators

theorem realEnergy_damped_node_mem {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    realEnergyRho e x * x ∈ Ioo (-1 : ℝ) 1 := by
  have hr := realEnergyRho_mem he hx
  exact energy_mul_mem_Ioo ⟨by linarith [hr.1], hr.2⟩ hx

theorem energy_hasSum_power_square {N : ℕ} (e : ℝ) (x : Fin (n N) → ℝ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => realEnergyPowerMoment N e x k ^ 2 / (k : ℝ))
      (-(∑ i : Fin (n N), ∑ j : Fin (n N),
        Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
          (n N : ℝ) ^ 2) := by
  have hp (i j : Fin (n N)) := energy_hasSum_mul_power_div
    (realEnergy_damped_node_mem he (hx i)) (realEnergy_damped_node_mem he (hx j))
  have hs : HasSum
      (fun k : ℕ => ∑ i : Fin (n N), ∑ j : Fin (n N),
        ((realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j)) ^ k / (k : ℝ))
      (∑ i : Fin (n N), ∑ j : Fin (n N),
        -Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => hp i j))
  have hc (k : ℕ) :
      (∑ i : Fin (n N), ∑ j : Fin (n N),
        ((realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j)) ^ k / (k : ℝ)) =
      (∑ i : Fin (n N), realEnergyRho e (x i) ^ k * x i ^ k) ^ 2 / (k : ℝ) := by
    simp only [mul_pow]
    simpa only [one_mul, pow_two] using energy_sum_sum_mul_div
      (fun i : Fin (n N) => realEnergyRho e (x i) ^ k * x i ^ k)
      (fun i : Fin (n N) => realEnergyRho e (x i) ^ k * x i ^ k) 1 (k : ℝ)
  convert hs.mul_left (1 / (n N : ℝ) ^ 2) using 1
  · ext k
    rw [hc]
    unfold realEnergyPowerMoment
    simp only [div_eq_mul_inv]
    ring
  · simp only [Finset.sum_neg_distrib]
    ring

theorem energy_hasSum_column_square {N : ℕ} (hN : 0 < N)
    (e : ℝ) (s : Fin (n N) → ℝ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ => 2 * realEnergyColumnMoment N e s k ^ 2 / (k : ℝ))
      (-(∑ i : Fin (n N), ∑ j : Fin (n N),
        realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
          (n N : ℝ) ^ 2 - Real.log 2) := by
  have hn0 : (n N : ℝ) ≠ 0 := by exact_mod_cast (show n N ≠ 0 by unfold n; omega)
  have hs' (i : Fin (n N)) : s i ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [(hs i).1], (hs i).2.le⟩
  have hr (i j : Fin (n N)) :
      realEnergySigma e (s i) * realEnergySigma e (s j) ∈ Ico (0 : ℝ) 1 :=
    ⟨(mul_pos (realEnergySigma_mem he (hs i)).1 (realEnergySigma_mem he (hs j)).1).le,
      (realEnergySigma_mul_bounds he (hs i) (hs j)).2⟩
  have hp (i j : Fin (n N)) := energy_hasSum_cosine_kernel (hr i j) (hs' i) (hs' j)
  have hh : HasSum
      (fun k : ℕ => ∑ i : Fin (n N), ∑ j : Fin (n N),
        2 * (realEnergySigma e (s i) * realEnergySigma e (s j)) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s i) * (Chebyshev.T ℝ (k : ℤ)).eval (s j) / (k : ℝ))
      (∑ i : Fin (n N), ∑ j : Fin (n N),
        (-realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j) -
          Real.log 2)) := hasSum_sum (fun i _ => hasSum_sum (fun j _ => hp i j))
  have hc (k : ℕ) :
      (∑ i : Fin (n N), ∑ j : Fin (n N),
        2 * (realEnergySigma e (s i) * realEnergySigma e (s j)) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s i) * (Chebyshev.T ℝ (k : ℤ)).eval (s j) / (k : ℝ)) =
      2 * (∑ i : Fin (n N), realEnergySigma e (s i) ^ k *
        (Chebyshev.T ℝ (k : ℤ)).eval (s i)) ^ 2 / (k : ℝ) := by
    calc
      _ = ∑ i : Fin (n N), ∑ j : Fin (n N),
          2 * (realEnergySigma e (s i) ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (s i)) *
            (realEnergySigma e (s j) ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (s j)) / (k : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow]
        ring
      _ = _ := by rw [energy_sum_sum_mul_div]; ring
  convert hh.mul_left (1 / (n N : ℝ) ^ 2) using 1
  · ext k
    rw [hc]
    unfold realEnergyColumnMoment
    simp only [div_eq_mul_inv]
    ring
  · simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul]
    field_simp [hn0]

theorem energy_hasSum_mixed_moments {N : ℕ} (e : ℝ) (x s : Fin (n N) → ℝ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ => 2 * realEnergyPowerMoment N e x k *
      realEnergyColumnMoment N e s k / (k : ℝ))
      (-(∑ i : Fin (n N), ∑ j : Fin (n N),
        Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
          (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / (n N : ℝ) ^ 2) := by
  have hs' (j : Fin (n N)) : s j ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [(hs j).1], (hs j).2.le⟩
  have hz (i j : Fin (n N)) :
      realEnergyRho e (x i) * realEnergySigma e (s j) * x i ∈ Ioo (-1 : ℝ) 1 := by
    have hr := realEnergyRho_mem he (hx i)
    have ht := realEnergySigma_mem he (hs j)
    exact energy_mul_mem_Ioo
      (energy_mul_mem_Ioo ⟨by linarith [hr.1], hr.2⟩ ⟨by linarith [ht.1], ht.2⟩) (hx i)
  have hp (i j : Fin (n N)) := energy_hasSum_cross_kernel (hz i j) (hs' j)
  have hh : HasSum
      (fun k : ℕ => ∑ i : Fin (n N), ∑ j : Fin (n N),
        2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s j) / (k : ℝ))
      (∑ i : Fin (n N), ∑ j : Fin (n N),
        -Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
          (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => hp i j))
  have hc (k : ℕ) :
      (∑ i : Fin (n N), ∑ j : Fin (n N),
        2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s j) / (k : ℝ)) =
      2 * (∑ i : Fin (n N), realEnergyRho e (x i) ^ k * x i ^ k) *
        (∑ j : Fin (n N), realEnergySigma e (s j) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s j)) / (k : ℝ) := by
    calc
      _ = ∑ i : Fin (n N), ∑ j : Fin (n N),
          2 * (realEnergyRho e (x i) ^ k * x i ^ k) *
            (realEnergySigma e (s j) ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (s j)) / (k : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [mul_pow]
        ring
      _ = _ := energy_sum_sum_mul_div _ _ _ _
  convert hh.mul_left (1 / (n N : ℝ) ^ 2) using 1
  · ext k
    rw [hc]
    unfold realEnergyPowerMoment realEnergyColumnMoment
    simp only [div_eq_mul_inv]
    ring
  · simp only [Finset.sum_neg_distrib]
    ring

theorem energy_hasSum_second_square {N : ℕ} (hN : 0 < N)
    (e : ℝ) (x s : Fin (n N) → ℝ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ =>
      (realEnergyPowerMoment N e x k - 2 * realEnergyColumnMoment N e s k) ^ 2 / (2 * (k : ℝ)))
      (-((∑ i : Fin (n N), ∑ j : Fin (n N),
          Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
            (2 * (n N : ℝ) ^ 2) +
        (∑ i : Fin (n N), ∑ j : Fin (n N),
          realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
            (n N : ℝ) ^ 2 -
        (∑ i : Fin (n N), ∑ j : Fin (n N),
          Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
            (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / (n N : ℝ) ^ 2 +
        Real.log 2)) := by
  have hp := (energy_hasSum_power_square e x he hx).mul_left (1 / 2 : ℝ)
  have hc := energy_hasSum_column_square hN e s he hs
  have hm := energy_hasSum_mixed_moments e x s he hx hs
  convert (hp.add hc).sub hm using 1
  · ext k
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem energy_hasSum_trialTau_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {N : ℕ} {e : ℝ}
    {x : Fin (n N) → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => u (k + 1) * realEnergyCosineMoment N e x (k + 1) /
        ((k + 1 : ℕ) : ℝ))
      ((∑ i : Fin (n N), realEnergyTrialTau u e (x i)) / (n N : ℝ)) := by
  have hs : HasSum
      (fun k : ℕ => ∑ i : Fin (n N),
        u (k + 1) * realEnergyTau e ^ (k + 1) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (x i) / ((k + 1 : ℕ) : ℝ))
      (∑ i : Fin (n N), realEnergyTrialTau u e (x i)) := by
    apply hasSum_sum
    intro i hi
    exact (realEnergyTrialTau_summable u hu he (hx i)).hasSum
  convert hs.div_const (n N : ℝ) using 1
  funext k
  simp only [realEnergyCosineMoment, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem energy_hasSum_trialRho_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {N : ℕ} {e : ℝ}
    {x : Fin (n N) → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => u (k + 1) * realEnergyPowerMoment N e x (k + 1) /
        ((k + 1 : ℕ) : ℝ))
      ((∑ i : Fin (n N), realEnergyTrialRho u e (x i)) / (n N : ℝ)) := by
  have hs : HasSum
      (fun k : ℕ => ∑ i : Fin (n N),
        u (k + 1) * realEnergyRho e (x i) ^ (k + 1) * x i ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ))
      (∑ i : Fin (n N), realEnergyTrialRho u e (x i)) := by
    apply hasSum_sum
    intro i hi
    exact (realEnergyTrialRho_summable u hu he (hx i)).hasSum
  convert hs.div_const (n N : ℝ) using 1
  funext k
  simp only [realEnergyPowerMoment, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem energy_hasSum_trialSigma_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {N : ℕ} {e : ℝ}
    {s : Fin (n N) → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ => u (k + 1) * realEnergyColumnMoment N e s (k + 1) /
        ((k + 1 : ℕ) : ℝ))
      ((∑ j : Fin (n N), realEnergyTrialSigma u e (s j)) / (n N : ℝ)) := by
  have hh : HasSum
      (fun k : ℕ => ∑ j : Fin (n N),
        u (k + 1) * realEnergySigma e (s j) ^ (k + 1) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (s j) / ((k + 1 : ℕ) : ℝ))
      (∑ j : Fin (n N), realEnergyTrialSigma u e (s j)) := by
    apply hasSum_sum
    intro j hj
    exact (realEnergyTrialSigma_summable u hu he (hs j)).hasSum
  convert hh.div_const (n N : ℝ) using 1
  funext k
  simp only [realEnergyColumnMoment, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem energy_tsum_trialTau_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {N : ℕ} {e : ℝ}
    {x : Fin (n N) → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    (∑' k : ℕ, u (k + 1) * realEnergyCosineMoment N e x (k + 1) /
      ((k + 1 : ℕ) : ℝ)) =
      (∑ i : Fin (n N), realEnergyTrialTau u e (x i)) / (n N : ℝ) :=
  (energy_hasSum_trialTau_average u hu he hx).tsum_eq

theorem energy_tsum_trialRho_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {N : ℕ} {e : ℝ}
    {x : Fin (n N) → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    (∑' k : ℕ, u (k + 1) * realEnergyPowerMoment N e x (k + 1) /
      ((k + 1 : ℕ) : ℝ)) =
      (∑ i : Fin (n N), realEnergyTrialRho u e (x i)) / (n N : ℝ) :=
  (energy_hasSum_trialRho_average u hu he hx).tsum_eq

theorem energy_tsum_trialSigma_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {N : ℕ} {e : ℝ}
    {s : Fin (n N) → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    (∑' k : ℕ, u (k + 1) * realEnergyColumnMoment N e s (k + 1) /
      ((k + 1 : ℕ) : ℝ)) =
      (∑ j : Fin (n N), realEnergyTrialSigma u e (s j)) / (n N : ℝ) :=
  (energy_hasSum_trialSigma_average u hu he hs).tsum_eq

end

open Set
open scoped BigOperators

theorem energy_tangent_of_hasSum (u a : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {K S : ℝ} (hK : 0 ≤ K)
    (ha : ∀ k, |a k| ≤ K)
    (hS : HasSum (fun k : ℕ => a (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) S) :
    -S ≤ barrierTrialNormSq u -
      2 * (∑' k : ℕ, u (k + 1) * a (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  have huS : HasSum (fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (barrierTrialNormSq u) := (energy_trial_norm_summable u hu).hasSum
  have hp := (energy_trial_product_summable u a hu hK ha).hasSum
  apply hasSum_le _ hS.neg (huS.sub (hp.mul_left 2))
  intro k
  have hbase : -a (k + 1) ^ 2 ≤ u (k + 1) ^ 2 - 2 * (u (k + 1) * a (k + 1)) := by
    nlinarith [sq_nonneg (a (k + 1) - u (k + 1))]
  convert div_le_div_of_nonneg_right hbase (Nat.cast_nonneg (k + 1)) using 1 <;> ring

theorem realEnergy_first_tangent {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (u : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    ((∑ i : Fin (n N), ∑ j : Fin (n N),
        realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) /
      (n N : ℝ) ^ 2 + Real.log 2) / 2 ≤
    barrierTrialNormSq u -
      2 * (∑' k : ℕ, u (k + 1) * realEnergyCosineMoment N e x (k + 1) /
        ((k + 1 : ℕ) : ℝ)) := by
  have hS : HasSum
      (fun k : ℕ => realEnergyCosineMoment N e x (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (-((∑ i : Fin (n N), ∑ j : Fin (n N),
          realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) /
        (n N : ℝ) ^ 2 + Real.log 2) / 2) := by
    apply (hasSum_nat_add_iff
      (f := fun k : ℕ => realEnergyCosineMoment N e x k ^ 2 / (k : ℝ)) 1).2
    simpa using energy_hasSum_first_square hN he hx
  have ht := energy_tangent_of_hasSum u (realEnergyCosineMoment N e x) hu
    (by norm_num : (0 : ℝ) ≤ 1) (energy_cosineMoment_abs_le_one hN he hx) hS
  linarith

theorem realEnergy_second_tangent {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (u : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    (∑ i : Fin (n N), ∑ j : Fin (n N),
      Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
        (2 * (n N : ℝ) ^ 2) +
    (∑ i : Fin (n N), ∑ j : Fin (n N),
      realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
        (n N : ℝ) ^ 2 -
    (∑ i : Fin (n N), ∑ j : Fin (n N),
      Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
        (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / (n N : ℝ) ^ 2 +
      Real.log 2 ≤
    barrierTrialNormSq u / 2 -
      (∑' k : ℕ, u (k + 1) * realEnergyPowerMoment N e x (k + 1) / ((k + 1 : ℕ) : ℝ)) +
      2 * (∑' k : ℕ, u (k + 1) * realEnergyColumnMoment N e s (k + 1) /
        ((k + 1 : ℕ) : ℝ)) := by
  let a : ℕ → ℝ := fun k => realEnergyPowerMoment N e x k - 2 * realEnergyColumnMoment N e s k
  have hB := energy_trial_product_summable u (realEnergyPowerMoment N e x) hu
    (by norm_num : (0 : ℝ) ≤ 1) (energy_powerMoment_abs_le_one hN he hx)
  have hC := energy_trial_product_summable u (realEnergyColumnMoment N e s) hu
    (by norm_num : (0 : ℝ) ≤ 1) (energy_columnMoment_abs_le_one hN he hs)
  have hsplit :
      (∑' k : ℕ, u (k + 1) * a (k + 1) / ((k + 1 : ℕ) : ℝ)) =
      (∑' k : ℕ, u (k + 1) * realEnergyPowerMoment N e x (k + 1) / ((k + 1 : ℕ) : ℝ)) -
      2 * (∑' k : ℕ, u (k + 1) * realEnergyColumnMoment N e s (k + 1) /
        ((k + 1 : ℕ) : ℝ)) := by
    apply HasSum.tsum_eq
    convert hB.hasSum.sub (hC.hasSum.mul_left 2) using 1
    funext k
    dsimp [a]
    ring
  have hhalf := energy_hasSum_second_square hN e x s he hx hs
  have hfull := hhalf.mul_left 2
  have hS : HasSum (fun k : ℕ => a (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (2 * (-((∑ i : Fin (n N), ∑ j : Fin (n N),
          Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
            (2 * (n N : ℝ) ^ 2) +
        (∑ i : Fin (n N), ∑ j : Fin (n N),
          realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
            (n N : ℝ) ^ 2 -
        (∑ i : Fin (n N), ∑ j : Fin (n N),
          Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
            (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / (n N : ℝ) ^ 2 +
        Real.log 2))) := by
    apply (hasSum_nat_add_iff (f := fun k : ℕ => a k ^ 2 / (k : ℝ)) 1).2
    simp only [Finset.sum_range_one, Nat.cast_zero, div_zero, add_zero]
    convert hfull using 1
    funext k
    dsimp [a]
    ring
  have ht := energy_tangent_of_hasSum u a hu (by norm_num : (0 : ℝ) ≤ 3)
    (energy_secondMoment_abs_le_three hN he hx hs) hS
  rw [hsplit] at ht
  linarith

def realEnergyDampedInteraction (N : ℕ) (k e : ℝ) (x s : Fin (n N) → ℝ) : ℝ :=
  (k / 2) *
    (∑ i : Fin (n N), ∑ j : Fin (n N),
      realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) / (n N : ℝ) ^ 2 +
  (∑ i : Fin (n N), ∑ j : Fin (n N),
    Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
      (2 * (n N : ℝ) ^ 2) +
  (∑ i : Fin (n N), ∑ j : Fin (n N),
    realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
      (n N : ℝ) ^ 2 -
  (∑ i : Fin (n N), ∑ j : Fin (n N),
    Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
      (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / (n N : ℝ) ^ 2

theorem realEnergyDampedInteraction_eq_squares {N : ℕ} (hN : 0 < N)
    (k : ℝ) {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    realEnergyDampedInteraction N k e x s = -(k / 2 + 1) * Real.log 2 -
      k * (∑' j : ℕ, realEnergyCosineMoment N e x j ^ 2 / (j : ℝ)) -
      (∑' j : ℕ, (realEnergyPowerMoment N e x j - 2 * realEnergyColumnMoment N e s j) ^ 2 /
        (2 * (j : ℝ))) := by
  rw [(energy_hasSum_first_square hN he hx).tsum_eq,
    (energy_hasSum_second_square hN e x s he hx hs).tsum_eq]
  unfold realEnergyDampedInteraction
  ring

theorem realEnergyDampedInteraction_le_trials {N : ℕ} (hN : 0 < N)
    {k e : ℝ} (hk : 0 ≤ k) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|)) :
    realEnergyDampedInteraction N k e x s ≤ -(k / 2 + 1) * Real.log 2 +
      k * barrierTrialNormSq p + barrierTrialNormSq v / 2 -
      2 * k * (∑' j : ℕ, p (j + 1) * realEnergyCosineMoment N e x (j + 1) /
        ((j + 1 : ℕ) : ℝ)) -
      (∑' j : ℕ, v (j + 1) * realEnergyPowerMoment N e x (j + 1) / ((j + 1 : ℕ) : ℝ)) +
      2 * (∑' j : ℕ, v (j + 1) * realEnergyColumnMoment N e s (j + 1) /
        ((j + 1 : ℕ) : ℝ)) := by
  have hfirst := mul_le_mul_of_nonneg_left (realEnergy_first_tangent hN he hx p hp) hk
  have hsecond := realEnergy_second_tangent hN he hx hs v hv
  unfold realEnergyDampedInteraction
  simp only [div_eq_mul_inv, mul_inv_rev] at hfirst hsecond ⊢
  nlinarith only [hfirst, hsecond]

open Set
open scoped BigOperators

theorem energy_average_le_of_le_add {m : ℕ} (hm : 0 < m)
    (f g : Fin m → ℝ) (c : ℝ) (hfg : ∀ i, f i ≤ g i + c) :
    (∑ i, f i) / (m : ℝ) ≤ (∑ i, g i) / (m : ℝ) + c := by
  have hmp : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hfg i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hh
  calc
    _ ≤ ((∑ i, g i) + (m : ℝ) * c) / (m : ℝ) :=
      div_le_div_of_nonneg_right hh hmp.le
    _ = _ := by field_simp [hmp.ne']

theorem realEnergyDampedInteraction_le_trialAverages {N : ℕ} (hN : 0 < N)
    {k e : ℝ} (hk : 0 ≤ k) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|)) :
    realEnergyDampedInteraction N k e x s ≤ -(k / 2 + 1) * Real.log 2 +
      k * barrierTrialNormSq p + barrierTrialNormSq v / 2 +
      (∑ i : Fin (n N), (-2 * k * realEnergyTrialTau p e (x i) - realEnergyTrialRho v e (x i))) /
        (n N : ℝ) +
      (∑ j : Fin (n N), 2 * realEnergyTrialSigma v e (s j)) / (n N : ℝ) := by
  have hh := realEnergyDampedInteraction_le_trials hN hk he hx hs p v hp hv
  rw [energy_tsum_trialTau_average p hp he hx,
    energy_tsum_trialRho_average v hv he hx, energy_tsum_trialSigma_average v hv he hs] at hh
  apply hh.trans_eq
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem realEnergyDampedInteraction_le_canonicalTrials {N : ℕ} (hN : 0 < N)
    {k e : ℝ} (hk : 0 ≤ k) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|)) :
    realEnergyDampedInteraction N k e x s ≤ -(k / 2 + 1) * Real.log 2 +
      k * barrierTrialNormSq p + barrierTrialNormSq v / 2 +
      (∑ i : Fin (n N), (-2 * k * barrierTrialT p (x i) - barrierTrialS v (x i))) / (n N : ℝ) +
      (∑ j : Fin (n N), 2 * barrierTrialT v (s j)) / (n N : ℝ) +
      2 * k * e * (∑' j : ℕ, |p j|) + 4 * e * (∑' j : ℕ, |v j|) := by
  have hn : 0 < n N := by unfold n; omega
  have hxavg := energy_average_le_of_le_add hn
    (fun i => -2 * k * realEnergyTrialTau p e (x i) - realEnergyTrialRho v e (x i))
    (fun i => -2 * k * barrierTrialT p (x i) - barrierTrialS v (x i))
    (2 * k * e * (∑' j : ℕ, |p j|) + 2 * e * (∑' j : ℕ, |v j|)) (fun i => by
      have ht := (abs_le.mp (realEnergyTrialTau_sub_le p hp he (hx i))).1
      have hr := (abs_le.mp (realEnergyTrialRho_sub_le v hv he (hx i))).1
      have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * k by positivity)
      nlinarith only [hm, hr])
  have hsavg := energy_average_le_of_le_add hn
    (fun j => 2 * realEnergyTrialSigma v e (s j))
    (fun j => 2 * barrierTrialT v (s j))
    (2 * e * (∑' j : ℕ, |v j|)) (fun j => by
      have ht := (abs_le.mp (realEnergyTrialSigma_sub_le v hv he (hs j))).2
      linarith)
  have hd := realEnergyDampedInteraction_le_trialAverages hN hk he hx hs p v hp hv
  linarith

end InternalCatalan

end

end OAI
