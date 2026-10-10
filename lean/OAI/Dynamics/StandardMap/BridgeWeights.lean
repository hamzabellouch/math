import OAI.Dynamics.StandardMap.NonlinearDirichlet

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma weighted_green_exponent (l p : ℕ) :
    (4/5:ℝ)*((l:ℝ)+1)+(min l p:ℕ)-(9/10)*((max l p:ℕ)+1)+1-
      (8/5)*((p:ℝ)+1) ≤ -(1/10)-(3/5)*((p:ℝ)+1) := by
  have hl : (0:ℝ) ≤ l := Nat.cast_nonneg _
  have hp : (0:ℝ) ≤ p := Nat.cast_nonneg _
  rcases le_total l p with h|h
  · rw [min_eq_left h,max_eq_right h]
    have hh : (l:ℝ) ≤ p := by exact_mod_cast h
    linarith
  · rw [min_eq_right h,max_eq_left h]
    linarith
lemma finite_green_weight_sum (M : ℝ) (hM : 1 < M) (hq : M^(-(3/5:ℝ)) ≤ 1/2) (n : ℕ) :
    ∑ i : Fin n, M^(-(1/10:ℝ)-(3/5)*((i:ℝ)+1)) ≤ 2*M^(-(7/10:ℝ)) := by
  have hp : 0 < M := by linarith
  have he (i : Fin n) : M^(-(1/10:ℝ)-(3/5)*((i:ℝ)+1)) =
      M^(-(7/10:ℝ))*(M^(-(3/5:ℝ)))^(i:ℕ) := by
    rw [← Real.rpow_mul_natCast hp.le,← Real.rpow_add hp]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range]
  have hs : ∑ i ∈ Finset.range n, (M^(-(3/5:ℝ)))^i ≤ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (1/2:ℝ)^i := by gcongr
      _ ≤ 2 := sum_geometric_two_le n
  nlinarith [Real.rpow_pos_of_pos hp (-(7/10:ℝ))]

lemma green_weighted_rows (M C R : ℝ) (n : ℕ) (t U : ℕ → ℝ)
    (hM : 1 < M) (hC : 0 ≤ C) (hR : 0 ≤ R) (hq : M^(-(3/5:ℝ)) ≤ 1/2)
    (ht : ∀ p, 1 ≤ p → p ≤ n → |t p| ≤ M^((p:ℝ)-1))
    (hU : ∀ p, 1 ≤ p → p ≤ n → |U p| ≤ C*M^(-(9/10:ℝ)*(p:ℝ))) :
    ∀ i : Fin n,
      ∑ j : Fin n,
        |M^((4/5:ℝ)*((i:ℝ)+1))*(t (min (i:ℕ) (j:ℕ)+1)*U (max (i:ℕ) (j:ℕ)+1))| *
          ((2*Real.pi*M)*R/M^((4/5:ℝ)*((j:ℝ)+1)))/M^((4/5:ℝ)*((j:ℝ)+1)) ≤
        (4*Real.pi*C*R)*M^(-(7/10:ℝ)) := by
  have hp : 0 < M := by linarith
  intro i
  calc
    _ ≤ ∑ j : Fin n, (2*Real.pi*C*R)*M^(-(1/10:ℝ)-(3/5)*((j:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hmin : min (i:ℕ) (j:ℕ)+1 ≤ n := by have:=min_le_left (i:ℕ) (j:ℕ); omega
      have hmax : max (i:ℕ) (j:ℕ)+1 ≤ n := by omega
      have ht' := ht _ (by omega) hmin
      have hU' := hU _ (by omega) hmax
      rw [abs_mul,abs_of_pos (Real.rpow_pos_of_pos hp _),abs_mul]
      calc
        _ ≤ M^((4/5:ℝ)*((i:ℝ)+1))*(M^((min (i:ℕ) (j:ℕ):ℝ))*(C*M^(-(9/10:ℝ)*((max (i:ℕ) (j:ℕ):ℝ)+1)))) *
          ((2*Real.pi*M)*R/M^((4/5:ℝ)*((j:ℝ)+1)))/M^((4/5:ℝ)*((j:ℝ)+1)) := by
            gcongr
            · simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Nat.cast_min] using ht'
            · simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_max] using hU'
        _ = (2*Real.pi*C*R)*M^((4/5:ℝ)*((i:ℝ)+1)+(min (i:ℕ) (j:ℕ):ℝ)-
            (9/10)*((max (i:ℕ) (j:ℕ):ℝ)+1)+1-(8/5)*((j:ℝ)+1)) := by
          rw [show (4/5:ℝ)*((i:ℝ)+1)+(min (i:ℕ) (j:ℕ):ℝ)-
            (9/10)*((max (i:ℕ) (j:ℕ):ℝ)+1)+1-(8/5)*((j:ℝ)+1) =
            ((4/5:ℝ)*((i:ℝ)+1)+(min (i:ℕ) (j:ℕ):ℝ)+
            (-(9/10)*((max (i:ℕ) (j:ℕ):ℝ)+1))+1)-
            ((4/5)*((j:ℝ)+1)+(4/5)*((j:ℝ)+1)) by ring]
          rw [Real.rpow_sub hp]
          simp only [Real.rpow_add hp,Real.rpow_one]
          ring

        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hM.le (by simpa only [Nat.cast_min,Nat.cast_max] using weighted_green_exponent i j)) (by positivity)
    _ = (2*Real.pi*C*R)*∑ j : Fin n, M^(-(1/10:ℝ)-(3/5)*((j:ℝ)+1)) := by rw [Finset.mul_sum]
    _ ≤ (2*Real.pi*C*R)*(2*M^(-(7/10:ℝ))) :=
      mul_le_mul_of_nonneg_left (finite_green_weight_sum M hM hq n) (by positivity)
    _ = _ := by ring
end StandardMapEntropy

end OAI
