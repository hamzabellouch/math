import Mathlib

namespace OAI

/-! Spin Tails. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology

 
def fallingRatio (Q z : ℕ) : ℝ :=
  (Q.descFactorial z : ℝ) / ((2 * Q - 2).descFactorial z : ℝ)

 

def gramShift (Q z : ℕ) : ℝ :=
  (-1 : ℝ)^z * fallingRatio Q z * (3 * z - 1 - z * (z + 1) / Q)

theorem fallingRatio_nonneg (Q z : ℕ) : 0 ≤ fallingRatio Q z := by
  unfold fallingRatio
  positivity

theorem fallingRatio_succ {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    fallingRatio Q (z + 1) =
      ((Q : ℝ) - z) / (2 * Q - 2 - z) * fallingRatio Q z := by
  unfold fallingRatio
  rw [Nat.descFactorial_succ, Nat.descFactorial_succ,
    Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm,
    Nat.cast_sub hz, Nat.cast_sub (show z ≤ 2*Q-2 by omega),
    Nat.cast_sub (show 2 ≤ 2*Q by omega)]
  push_cast
  rfl

 
theorem fallingRatio_le_geometric {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    fallingRatio Q z ≤ (2 / 3 : ℝ)^z := by
  induction z with
  | zero => simp [fallingRatio]
  | succ z ih =>
    rw [fallingRatio_succ (by omega) (by omega), pow_succ']
    have hQR : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hzR : (z : ℝ) + 1 ≤ Q := by exact_mod_cast hz
    have hd : 0 < 2 * (Q : ℝ) - 2 - z := by linarith
    have hf : ((Q : ℝ)-z) / (2*Q-2-z) ≤ 2/3 := by
      rw [div_le_iff₀ hd]
      have : (0 : ℝ) ≤ z := Nat.cast_nonneg z
      linarith
    exact mul_le_mul hf (ih (by omega)) (fallingRatio_nonneg Q z) (by norm_num)

private theorem affineRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => ((Q : ℝ)-z)/(2*Q-2-z)) atTop (𝓝 (1/2)) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (z : ℝ)
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (2 + (z : ℝ))
  have hh : Tendsto (fun Q : ℕ => (1 - (z : ℝ)/Q)/(2 - (2+z)/Q))
      atTop (𝓝 (1/2)) := by
    convert ((tendsto_const_nhds (x := (1:ℝ))).sub h1).div
      ((tendsto_const_nhds (x := (2:ℝ))).sub h2)
      (show (2:ℝ)-0 ≠ 0 by norm_num) using 1
    first | rfl | norm_num
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (z+2)] with Q hQ
  have hn : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hzr : (z : ℝ) + 2 ≤ Q := by exact_mod_cast hQ
  have hd : 2 * (Q:ℝ) - 2 - z ≠ 0 := by have := Nat.cast_nonneg (α:=ℝ) z; linarith
  have hd' : 2 - (2 + (z:ℝ)) / Q ≠ 0 := by
    rw [ne_eq, sub_eq_zero, eq_div_iff hn]
    linarith
  field_simp [hn, hd, hd']
  ring

theorem fallingRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => fallingRatio Q z) atTop (𝓝 ((1/2 : ℝ)^z)) := by
  induction z with
  | zero => simp [fallingRatio]
  | succ z ih =>
    have h := (affineRatio_tendsto z).mul ih
    simp only [← pow_succ'] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (z+2)] with Q hQ
    exact (fallingRatio_succ (by omega) (by omega)).symm

 
theorem gramShift_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => gramShift Q z) atTop
      (𝓝 ((3 * (z : ℝ) - 1) * (-1/2)^z)) := by
  have h := ((fallingRatio_tendsto z).const_mul ((-1:ℝ)^z)).mul
    ((tendsto_const_nhds (x := (3*(z:ℝ)-1))).sub
      (tendsto_const_div_atTop_nhds_zero_nat ((z:ℝ)*(z+1))))
  convert h using 1
  · simp [gramShift]
  · simp only [sub_zero]
    rw [mul_assoc, mul_comm ((3*(z:ℝ)-1)), ← mul_assoc, ← mul_pow]
    congr 1
    norm_num

 
def spinRatio (Q z : ℕ) : ℝ :=
  (3 * Q - 1 - 2 * (z : ℝ)) / (2 * Q - 1)

theorem spinRatio_bounds {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    0 ≤ spinRatio Q z ∧ spinRatio Q z ≤ 2 := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hzR : (z : ℝ) ≤ Q := by exact_mod_cast hz
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  have hd : 0 < 2 * (Q : ℝ) - 1 := by linarith
  constructor
  · exact div_nonneg (by linarith) hd.le
  · rw [spinRatio, div_le_iff₀ hd]
    linarith

private theorem gramBracket_bounds {Q z : ℕ} (hQ : 1 ≤ Q)
    (hz1 : 1 ≤ z) (hzQ : z ≤ Q) :
    0 ≤ 3 * (z : ℝ) - 1 - z * (z + 1) / Q ∧
      3 * (z : ℝ) - 1 - z * (z + 1) / Q ≤ 3 * z := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hzR : (1 : ℝ) ≤ z := by exact_mod_cast hz1
  have hzQR : (z : ℝ) ≤ Q := by exact_mod_cast hzQ
  have hd : (z : ℝ) * (z + 1) / Q ≤ z + 1 := by
    rw [div_le_iff₀ hQR]
    nlinarith
  have hn : (0 : ℝ) ≤ (z : ℝ) * (z + 1) / Q := by positivity
  constructor <;> linarith

 
theorem gramShift_abs_le {Q z : ℕ} (hQ : 4 ≤ Q) (hz1 : 1 ≤ z) (hzQ : z ≤ Q) :
    |gramShift Q z| ≤ 3 * (z : ℝ) * (2/3)^z := by
  obtain ⟨hb0, hb⟩ := gramBracket_bounds (by omega : 1 ≤ Q) hz1 hzQ
  rw [gramShift, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (fallingRatio_nonneg Q z), abs_of_nonneg hb0]
  calc
    _ ≤ (2/3 : ℝ)^z * (3*z) :=
      mul_le_mul (fallingRatio_le_geometric hQ hzQ) hb hb0 (by positivity)
    _ = _ := mul_comm _ _

theorem spinRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => spinRatio Q z) atTop (𝓝 (3/2)) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (1+2*(z:ℝ))
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)
  have hh : Tendsto (fun Q : ℕ => (3 - (1+2*(z:ℝ))/Q)/(2 - 1/(Q:ℝ)))
      atTop (𝓝 (3/2)) := by
    convert ((tendsto_const_nhds (x := (3:ℝ))).sub h1).div
      ((tendsto_const_nhds (x := (2:ℝ))).sub h2) (show (2:ℝ)-0 ≠ 0 by norm_num)
      using 1
    first | rfl | norm_num
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  have hn : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hqr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hd : 2*(Q:ℝ)-1 ≠ 0 := by linarith
  have hd' : 2 - 1/(Q:ℝ) ≠ 0 := by
    rw [ne_eq, sub_eq_zero, eq_div_iff hn]
    linarith
  unfold spinRatio
  field_simp [hn, hd, hd']
  ring

 

def tailTerm (Q m : ℕ) : ℝ :=
  let z := 17 + 2*m
  if z ≤ Q then spinRatio Q z * |gramShift Q z| * (z+1) else 0

 
def tailCoefficient (Q : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (Q+1), tailTerm Q m

 

theorem tailTerm_bound {Q : ℕ} (hQ : 4 ≤ Q) (m : ℕ) :
    ‖tailTerm Q m‖ ≤
      6 * ((17+2*m : ℕ) : ℝ) * ((17+2*m : ℕ)+1) * (2/3 : ℝ)^(17+2*m) := by
  dsimp [tailTerm]
  split_ifs with hm
  · rw [abs_of_nonneg (by
      exact mul_nonneg (mul_nonneg (spinRatio_bounds (by omega) hm).1 (abs_nonneg _))
        (by positivity))]
    calc
      _ ≤ 2 * (3 * ((17+2*m : ℕ):ℝ) * (2/3)^(17+2*m)) * ((17+2*m : ℕ)+1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (spinRatio_bounds (by omega) hm).2
            (gramShift_abs_le hQ (by omega) hm) (abs_nonneg _) (by norm_num)) (by positivity)
      _ = _ := by ring
  · simp only [abs_zero]
    positivity

private theorem tailBound_summable :
    Summable (fun m : ℕ =>
      6 * ((17+2*m : ℕ) : ℝ) * ((17+2*m : ℕ)+1) * (2/3 : ℝ)^(17+2*m)) := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
    (show ‖(2/3 : ℝ)‖ < 1 by norm_num)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2
    (show ‖(2/3 : ℝ)‖ < 1 by norm_num)
  have h : Summable (fun z : ℕ => 6*(z:ℝ)*(z+1)*(2/3)^z) := by
    apply ((h2.mul_left 6).add (h1.mul_left 6)).congr
    intro z
    ring
  exact h.comp_injective (fun i j hij => by omega)

 
theorem tailTerm_tendsto (m : ℕ) :
    Tendsto (fun Q : ℕ => tailTerm Q m) atTop
      (𝓝 ((3/2 : ℝ)*(3*((17+2*m : ℕ):ℝ)-1)*
        (1/2 : ℝ)^(17+2*m)*((17+2*m : ℕ)+1))) := by
  let z := 17+2*m
  have hb : 0 ≤ 3*(z:ℝ)-1 := by dsimp [z]; push_cast; have := Nat.cast_nonneg (α:=ℝ) m; linarith
  have h := ((spinRatio_tendsto z).mul (gramShift_tendsto z).abs).mul_const ((z:ℝ)+1)
  have ha : |(-1/2 : ℝ)| = 1/2 := by norm_num
  rw [abs_mul, abs_pow, abs_of_nonneg hb, ha] at h
  have hh : (3/2 : ℝ)*((3*(z:ℝ)-1)*(1/2)^z)*((z:ℝ)+1) =
      (3/2 : ℝ)*(3*(z:ℝ)-1)*(1/2)^z*((z:ℝ)+1) := by ring
  rw [hh] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop z] with Q hQ
  simp [tailTerm, z, hQ]

 
theorem limit_tail_hasSum :
    HasSum (fun m : ℕ => (3/2 : ℝ)*(3*((17+2*m : ℕ):ℝ)-1)*
      (1/2 : ℝ)^(17+2*m)*((17+2*m : ℕ)+1)) (61/4096) := by
  have hr : ‖(1/4 : ℝ)‖ < 1 := by norm_num
  have h0 : HasSum (fun m : ℕ => (1/4 : ℝ)^m) (4/3) := by
    convert hasSum_geometric_of_lt_one (r := (1/4 : ℝ)) (by norm_num) (by norm_num) using 1
    norm_num
  have h1 : HasSum (fun m : ℕ => (m:ℝ)*(1/4 : ℝ)^m) (4/9) := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one hr using 1
    first | rfl | norm_num
  have h2 : HasSum (fun m : ℕ => ((m+2).choose 2 : ℝ)*(1/4 : ℝ)^m) (64/27) := by
    convert hasSum_choose_mul_geometric_of_norm_lt_one 2 hr using 1
    first | rfl | norm_num
  have h := (((h2.mul_left 24).add (h1.mul_left 172)).add (h0.mul_left 876)).mul_left
    ((3/2 : ℝ)*(1/2)^17)
  norm_num only [show (3/2 : ℝ)*(1/2)^17 * (24*(64/27)+172*(4/9)+876*(4/3)) =
    61/4096 by norm_num] at h
  apply h.congr_fun
  intro m
  rw [Nat.cast_choose_two]
  push_cast
  rw [pow_add, pow_mul]
  norm_num
  ring

 
theorem tailCoefficient_eq_tsum (Q : ℕ) : tailCoefficient Q = ∑' m, tailTerm Q m := by
  symm
  apply tsum_eq_sum
  intro m hm
  have hm' : Q+1 ≤ m := by simpa only [Finset.mem_range, not_lt] using hm
  have h : ¬ 17+2*m ≤ Q := by omega
  simp [tailTerm, h]

 

theorem tailCoefficient_tendsto :
    Tendsto tailCoefficient atTop (𝓝 (61/4096 : ℝ)) := by
  have h := tendsto_tsum_of_dominated_convergence tailBound_summable tailTerm_tendsto
    (show ∀ᶠ Q in atTop, ∀ m, ‖tailTerm Q m‖ ≤
      6 * ((17+2*m : ℕ) : ℝ) * ((17+2*m : ℕ)+1) * (2/3 : ℝ)^(17+2*m) from
      (eventually_ge_atTop 4).mono (fun _ hQ m => tailTerm_bound hQ m))
  rw [limit_tail_hasSum.tsum_eq] at h
  exact h.congr' (Filter.Eventually.of_forall (fun Q => (tailCoefficient_eq_tsum Q).symm))

 
theorem tailCoefficient_eq_odd_sum (Q : ℕ) :
    tailCoefficient Q =
      ∑ z ∈ (Finset.range (Q+1)).filter (fun z => 17 ≤ z ∧ Odd z),
        spinRatio Q z * |gramShift Q z| * (z+1) := by
  classical
  unfold tailCoefficient
  simp only [tailTerm]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun m _ => 17+2*m)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
    exact ⟨by omega, by omega, Nat.odd_iff.mpr (by omega)⟩
  · intro m hm n hn hmn
    omega
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_range, Nat.odd_iff] at hz
    refine ⟨(z-17)/2, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · omega
  · intro m hm
    rfl

theorem tailTerm_nonneg (Q m : ℕ) : 0 ≤ tailTerm Q m := by
  dsimp only [tailTerm]
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (spinRatio_bounds (by omega) h).1 (abs_nonneg _))
      (by positivity)
  · exact le_rfl

theorem tailCoefficient_nonneg (Q : ℕ) : 0 ≤ tailCoefficient Q :=
  Finset.sum_nonneg (fun m _ => tailTerm_nonneg Q m)

 

theorem allowance_count :
    (∑ D ∈ Finset.Icc 1 23, (D+1)^2 / 4) = (1222 : ℕ) := by
  decide
end LaughlinFock
end

end OAI
