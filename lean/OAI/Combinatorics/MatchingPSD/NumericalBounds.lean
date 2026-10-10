import OAI.Combinatorics.MatchingPSD.Parameters

namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix
open scoped BigOperators MatrixOrder

lemma blockSize_ge (d t : ℕ) : t^4 ≤ blockSize d t := by
  dsimp [blockSize]
  simpa only [one_mul] using Nat.mul_le_mul_right (t^4) (show 1 ≤ 4*(d+1) by omega)

lemma blockSize_grid (d t : ℕ) : 2*t^4*d ≤ blockSize d t := by
  dsimp [blockSize]
  calc
    2*t^4*d = (2*d)*t^4 := by ring
    _ ≤ 4*(d+1)*t^4 := Nat.mul_le_mul_right _ (by omega)

lemma selection_of_cleared {q r T m L b : ℝ} (hb : 0 < b) (hc : 0 < r*m*L)
    (hnum : q*r^6*T*m^2*L^2 ≤ b) :
    q*r^4*T*b⁻¹ ≤ (1/(r*m*L))^2 := by
  rw [← div_eq_mul_inv, div_pow, one_pow]
  apply (div_le_div_iff₀ hb (sq_pos_of_pos hc)).mpr
  calc
    _ = q*r^6*T*m^2*L^2 := by ring
    _ ≤ b := hnum
    _ = _ := by ring

lemma numerical_selection (p d t r n T : ℕ) (ht : 2 ≤ t) (hr : 0 < r)
    (hn : n ≤ t^6) (hT : T ≤ t) (hrn : (r:ℝ) ≤ (n:ℝ)^p) :
    (t:ℝ)*r^4*T*((2*(3*(blockSize d t:ℝ)+1))^(2*(10*(p+1))))⁻¹ ≤
      (1/((r:ℝ)*((n:ℝ)+1)*(2*(t:ℝ)^4)))^2 := by
  have ht2 : (2:ℝ) ≤ t := by exact_mod_cast ht
  have ht1 : (1:ℝ) ≤ t := by linarith
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hn6 : (n:ℝ) ≤ (t:ℝ)^6 := by exact_mod_cast hn
  have hrp : (r:ℝ) ≤ (t:ℝ)^(6*p) := by
    simpa only [pow_mul] using hrn.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) hn6 p)
  have hm : (n:ℝ)+1 ≤ (t:ℝ)^7 := by
    have h6 : (1:ℝ) ≤ (t:ℝ)^6 := one_le_pow₀ ht1
    calc
      _ ≤ (t:ℝ)^6+(t:ℝ)^6 := add_le_add hn6 h6
      _ = 2*(t:ℝ)^6 := by ring
      _ ≤ (t:ℝ)*(t:ℝ)^6 := mul_le_mul_of_nonneg_right ht2 (pow_nonneg ht0 _)
      _ = _ := by ring
  have hL : 2*(t:ℝ)^4 ≤ (t:ℝ)^5 := by
    calc
      _ ≤ (t:ℝ)*(t:ℝ)^4 := mul_le_mul_of_nonneg_right ht2 (pow_nonneg ht0 _)
      _ = _ := by ring
  have hTr : (T:ℝ) ≤ t := by exact_mod_cast hT
  have hbase : (t:ℝ)^4 ≤ 2*(3*(blockSize d t:ℝ)+1) := by
    have hs : (t:ℝ)^4 ≤ (blockSize d t:ℝ) := by exact_mod_cast blockSize_ge d t
    have hs0 : (0:ℝ) ≤ (blockSize d t:ℝ) := Nat.cast_nonneg _
    linarith
  have hb : 0 < (2*(3*(blockSize d t:ℝ)+1))^(2*(10*(p+1))) := by positivity
  apply selection_of_cleared hb (by positivity)
  calc
    _ ≤ (t:ℝ)*((t:ℝ)^(6*p))^6*(t:ℝ)*((t:ℝ)^7)^2*((t:ℝ)^5)^2 := by gcongr
    _ = (t:ℝ)^(36*p+26) := by
      have he : 36*p+26 = 1+(6*p)*6+1+7*2+5*2 := by omega
      rw [he]
      simp only [pow_add, pow_mul, pow_one]
    _ ≤ (t:ℝ)^(8*(10*(p+1))) := pow_le_pow_right₀ ht1 (by omega)
    _ = ((t:ℝ)^4)^(2*(10*(p+1))) := by rw [← pow_mul]; congr 1; omega
    _ ≤ _ := pow_le_pow_left₀ (pow_nonneg ht0 _) hbase _

lemma numerical_smallness (D : ℝ) (t : ℕ) (ht : 1 ≤ t) (hD : 8*(D+1) ≤ (t:ℝ)) :
    16*(t:ℝ)^2*((t:ℝ)*D+1) ≤ 2*(t:ℝ)^4 := by
  have ht1 : (1:ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
  calc
    _ ≤ 16*(t:ℝ)^2*((t:ℝ)*(D+1)) := by gcongr; linarith
    _ = 2*(t:ℝ)^3*(8*(D+1)) := by ring
    _ ≤ 2*(t:ℝ)^3*(t:ℝ) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by ring

end PerfectMatchingPSD

end OAI
