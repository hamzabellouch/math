import OAI.MeasureTheory.Falconer.Geometry.FinitePrefixBallBound
import OAI.MeasureTheory.Falconer.Estimates.LocalPacketRegularity

namespace OAI

/-! Finite relative prefix tests give the exact normalized ball bound in
an original cell chart, with its dyadic radius and fixed losses explicit. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem relative_dyadic_power {a n : ℕ} (ha : a ≤ n) (s : ℝ) :
    (1/(2:ℝ)^(n-a))^s = ((2:ℝ)^a)^s*(1/(2:ℝ)^n)^s := by
  have hp : (2:ℝ)^n = (2:ℝ)^a*(2:ℝ)^(n-a) := by rw [← pow_add,Nat.add_sub_of_le ha]
  have hb : 1/(2:ℝ)^(n-a) = (2:ℝ)^a*(1/(2:ℝ)^n) := by rw [hp]; field_simp
  rw [hb,Real.mul_rpow (by positivity : 0 ≤ (2:ℝ)^a) (by positivity : 0 ≤ 1/(2:ℝ)^n)]

theorem finite_relative_prefix_ball_bound_at {N M a : ℕ} (hMN : M ≤ N)
    (ha : a ≤ M) {s K : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (Q : DyadicCube 2) (hQ : Q.side = 1)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hprefix : ∀ n, a ≤ n → n ≤ M → ∀ p ∈ (P.image l).image (List.take n),
      ((pointPrefixFiber P l n p).card:ℝ) ≤ K*(1/(2:ℝ)^(n-a))^s*(P.card:ℝ))
    (y b : ℝ) :
    NormalizedFiniteBallBound (1/(2:ℝ)^(M-a)) s (49*K*4^s)
      (P.image (localPacketPoint (1/(2:ℝ)^a) y b)) := by
  have hpow : 1 ≤ ((2:ℝ)^a)^s := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hs
  have hK' : 1 ≤ K*((2:ℝ)^a)^s := by
    simpa using mul_le_mul hK hpow (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
  have htests : ∀ n ≤ M, ∀ p ∈ (P.image l).image (List.take n),
      ((pointPrefixFiber P l n p).card:ℝ) ≤ (K*((2:ℝ)^a)^s)*(1/(2:ℝ)^n)^s*(P.card:ℝ) := by
    intro n hn p hp
    by_cases han : a ≤ n
    · have hh := hprefix n han hn p hp
      rw [relative_dyadic_power han] at hh
      convert hh using 1; ring
    · have hn' : n ≤ a := Nat.le_of_not_ge han
      have hbase : 1 ≤ (2:ℝ)^a*(1/(2:ℝ)^n) := by
        rw [mul_one_div]
        exact (le_div_iff₀ (by positivity)).2 (by simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn')
      have hunit : 1 ≤ ((2:ℝ)^a)^s*(1/(2:ℝ)^n)^s := by
        rw [← Real.mul_rpow (by positivity : 0 ≤ (2:ℝ)^a) (by positivity : 0 ≤ 1/(2:ℝ)^n)]
        exact Real.one_le_rpow hbase hs
      have hk : 1 ≤ (K*((2:ℝ)^a)^s)*(1/(2:ℝ)^n)^s := by
        have hh := mul_le_mul hK hunit (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
        convert hh using 1 <;> ring
      exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans
        (le_mul_of_one_le_left (Nat.cast_nonneg _) hk)
  have hb := finite_prefix_ball_bound_at hMN hs hK' Q hQ P l hleaf htests
  have hl := localPacketPoint_regular (by positivity : 0 < 1/(2:ℝ)^M)
    (by positivity : 0 < 1/(2:ℝ)^a)
    ((div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))) y b P hb
  have heq : (1/(2:ℝ)^M)/(1/(2:ℝ)^a) = 1/(2:ℝ)^(M-a) := by
    have hp : (2:ℝ)^M = (2:ℝ)^a*(2:ℝ)^(M-a) := by rw [← pow_add,Nat.add_sub_of_le ha]
    rw [hp]
    field_simp
  have hcancel : ((2:ℝ)^a)^s*(1/(2:ℝ)^a)^s = 1 := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ (2:ℝ)^a) (by positivity : 0 ≤ 1/(2:ℝ)^a)]
    simp
  have hc : (49*(K*((2:ℝ)^a)^s)*4^s)*(1/(2:ℝ)^a)^s = 49*K*4^s := by
    calc
      _ = (49*K*4^s)*(((2:ℝ)^a)^s*(1/(2:ℝ)^a)^s) := by ring
      _ = _ := by rw [hcancel,mul_one]
  rwa [heq,hc] at hl

theorem finite_relative_prefix_ball_bound {N a : ℕ} (ha : a ≤ N) {s K : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (Q : DyadicCube 2) (hQ : Q.side = 1)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hprefix : ∀ n, a ≤ n → n ≤ N → ∀ p ∈ (P.image l).image (List.take n),
      ((pointPrefixFiber P l n p).card:ℝ) ≤ K*(1/(2:ℝ)^(n-a))^s*(P.card:ℝ))
    (y b : ℝ) :
    NormalizedFiniteBallBound (1/(2:ℝ)^(N-a)) s (49*K*4^s)
      (P.image (localPacketPoint (1/(2:ℝ)^a) y b)) :=
  finite_relative_prefix_ball_bound_at le_rfl ha hs hK Q hQ P l hleaf hprefix y b

end Falconer

end OAI
