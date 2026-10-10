import OAI.Dynamics.StandardMap.ScaleCancellation

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma bridge_error_geom (M : ℝ) (hM : (2:ℝ)^10≤ M) (N j : ℕ) (_hN : 1≤ N) :
    M^(-(1/10:ℝ)*((N*2^j:ℕ):ℝ))≤ (1/2:ℝ)^(N*2^j) := by
  have hMp : 0< M := lt_of_lt_of_le (by norm_num) hM
  have hbase : M^(-(1/10:ℝ))≤ (1/2:ℝ) := by
    rw [Real.rpow_neg hMp.le]
    apply (inv_le_comm₀ (Real.rpow_pos_of_pos hMp _) (by norm_num)).mpr
    have hh := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤ 2^10) hM (by norm_num : (0:ℝ)≤ 1/10)
    norm_num [←Real.rpow_natCast,←Real.rpow_mul] at hh
    simpa using hh
  rw [Real.rpow_mul_natCast hMp.le]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hMp.le _) hbase _
lemma half_pow_nat_le_inverse (N : ℕ) (hN : 1≤ N) : (1/2:ℝ)^N≤ 1/(N:ℝ) := by
  have hh : (N:ℝ)≤ (2:ℝ)^N := by exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := N)))
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by exact_mod_cast hN) hh
lemma bridge_error_inverse (M : ℝ) (hM : (2:ℝ)^10≤ M) (N j : ℕ) (hN : 1≤ N) :
    M^(-(1/10:ℝ)*((N*2^j:ℕ):ℝ))≤ 1/((N*2^j:ℕ):ℝ) :=
  (bridge_error_geom M hM N j hN).trans (half_pow_nat_le_inverse _ (by have : 0 < N*2^j := Nat.mul_pos (by omega) (by positivity); omega))
lemma bridge_error_sum (M : ℝ) (hM : (2:ℝ)^10≤ M) (N l : ℕ) (hN : 1≤ N) :
    (∑j∈Finset.range l,M^(-(1/10:ℝ)*((N*2^j:ℕ):ℝ)))≤ 2/(N:ℝ) := by
  calc
    _ ≤ ∑j∈Finset.range l,1/((N*2^j:ℕ):ℝ) := Finset.sum_le_sum (fun j _ => bridge_error_inverse M hM N j hN)
    _ = (1/(N:ℝ))*∑j∈Finset.range l,(1/2:ℝ)^j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      rw [div_pow,one_pow,one_div_mul_one_div]
    _ ≤ (1/(N:ℝ))*2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le l) (by positivity)
    _ = _ := by ring
lemma window_indices {a b : ℤ} {m r : ℕ}
    (ha : -(r:ℤ)≤ a-b) (hb : a+(m:ℤ)-b≤ r)
    (l : ℕ) (hl : 1≤ l) (hlm : l≤ m) : (a+(l:ℤ)-1-b).natAbs≤ r := by
  apply Nat.cast_le (α := ℤ) |>.mp
  rw [Int.natCast_natAbs,abs_le]
  constructor <;> omega
end StandardMapEntropy

end OAI
