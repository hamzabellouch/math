import OAI.NumberTheory.TwoPoint.Fourier.MinorArcTrivial

namespace OAI

/-! Finite halving of a prefix. The at most one omitted integer at each
halving step is absorbed in the dyadic allowance, without counting the
number of steps. -/

namespace TwoPointCorrelations

open Finset

theorem mrt_dyadic_prefix_bound (f : ℕ → ℝ) (X W : ℕ) (H ε : ℝ)
    (hW : 1 ≤ W) (hH : 0 ≤ H) (hε : 0 ≤ ε) (hbudget : 1 ≤ ε*W)
    (hpos : ∀ n, 0 ≤ f n) (hbound : ∀ n, f n ≤ H)
    (hdyadic : ∀ n : ℕ, W ≤ n → 2*n ≤ X →
      (∑ k ∈ Ico n (2*n), f k) ≤ ε*n*H) :
    (∑ n ∈ range X, f n) ≤ 2*ε*X*H+2*W*H := by
  have hprefix : ∀ m : ℕ, m ≤ X →
      (∑ n ∈ range m, f n) ≤ 2*ε*m*H+2*W*H := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hmX
      by_cases hm : m < 2*W
      · have hmR : (m:ℝ) ≤ 2*W := by exact_mod_cast (show m ≤ 2*W by omega)
        calc
          _ ≤ ∑ _n ∈ range m, H := sum_le_sum (fun n _ => hbound n)
          _ = (m:ℝ)*H := by simp
          _ ≤ 2*W*H := mul_le_mul_of_nonneg_right hmR hH
          _ ≤ 2*ε*m*H+2*W*H := le_add_of_nonneg_left (by positivity)
      · let n := m/2
        have hnW : W ≤ n := by dsimp [n]; omega
        have hnlt : n < m := by dsimp [n]; omega
        have hnX : n ≤ X := (Nat.le_of_lt hnlt).trans hmX
        have hnm : 2*n ≤ m := by dsimp [n]; omega
        have hmn : m ≤ 2*n+1 := by dsimp [n]; omega
        have hi := ih n hnlt hnX
        have hd := hdyadic n hnW (hnm.trans hmX)
        have hs : (∑ k ∈ range m, f k) ≤
            (∑ k ∈ range n, f k)+(∑ k ∈ Ico n (2*n), f k)+H := by
          calc
            _ ≤ ∑ k ∈ range (2*n+1), f k :=
              sum_le_sum_of_subset_of_nonneg (range_mono hmn) (fun k _ _ => hpos k)
            _ = (∑ k ∈ range (2*n), f k)+f (2*n) := sum_range_succ _ _
            _ ≤ (∑ k ∈ range (2*n), f k)+H := add_le_add le_rfl (hbound _)
            _ = _ := by rw [sum_range_add_sum_Ico _ (by omega : n ≤ 2*n)]
        have hnWR : (W:ℝ) ≤ n := by exact_mod_cast hnW
        have hen : 1 ≤ ε*n := hbudget.trans (mul_le_mul_of_nonneg_left hnWR hε)
        have hmR : 2*(n:ℝ) ≤ m := by exact_mod_cast hnm
        have hgap : H ≤ ε*n*H := by simpa using mul_le_mul_of_nonneg_right hen hH
        calc
          _ ≤ (2*ε*n*H+2*W*H)+(ε*n*H)+H := hs.trans (by linarith)
          _ ≤ 4*ε*n*H+2*W*H := by linarith
          _ ≤ 2*ε*m*H+2*W*H := by
            have hh := mul_le_mul_of_nonneg_left hmR (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hε) hH)
            nlinarith
  exact hprefix X le_rfl

end TwoPointCorrelations

end OAI
