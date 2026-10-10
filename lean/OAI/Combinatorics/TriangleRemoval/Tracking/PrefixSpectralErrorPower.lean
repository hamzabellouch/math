import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.LinkStarMatrix
import OAI.Combinatorics.TriangleRemoval.Asymptotics.OneAddLogRpow

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
open Filter

theorem prefixSpectralError_power_decay {c : ℝ} (hc : 0 < c) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      2 * prefixSpectralError n c ≤ (n : ℝ)^(-γ) := by
  let a : ℝ := min c (1/1000)
  let B : ℝ := (8000 : ℝ)^8001 * 2^8000
  let L : ℝ := 4 * (8001 + 2*B) ^ (1/(8000 : ℝ)) + 7
  have ha : 0 < a := lt_min hc (by norm_num)
  have hac : a ≤ c := min_le_left _ _
  have ha1 : a ≤ 1/1000 := min_le_right _ _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨a/16000,by positivity,?_⟩
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^(a/16000)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < a/16000)).comp tendsto_natCast_atTop_atTop
  filter_upwards [prefixD_eventual_envelope, eventually_ge_atTop (1 : ℕ),
    ht.eventually_ge_atTop (2*L)] with n hD hn hLr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hDr : 0 < (n : ℝ)^(1/1000 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hD0 : 0 < prefixD n := hDr.trans_le hD.1
  have hδ : (n : ℝ)^(-c) ≤ (n : ℝ)^(-a) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h4000 : ((n : ℝ)^(1/1000 : ℝ))^4000 = (n : ℝ)^(4 : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
    norm_num
  have hq : (n : ℝ)/prefixD n^4000 ≤ (n : ℝ)^(-a) := by
    calc
      _ ≤ (n : ℝ) / ((n : ℝ)^(1/1000 : ℝ))^4000 :=
        div_le_div_of_nonneg_left hn0.le (pow_pos hDr _)
          (pow_le_pow_left₀ hDr.le hD.1 _)
      _ = (n : ℝ)^(-(3 : ℝ)) := by
        rw [h4000]
        conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_sub hn0]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hi : 1/prefixD n ≤ (n : ℝ)^(-a) := by
    calc
      _ ≤ 1/(n : ℝ)^(1/1000 : ℝ) :=
        div_le_div_of_nonneg_left zero_le_one hDr hD.1
      _ = (n : ℝ)^(-(1/1000 : ℝ)) := by rw [Real.rpow_neg hn0.le,one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hsum : 8001*(n : ℝ)^(-c) + B*((n : ℝ)/prefixD n^4000 + 1/prefixD n) ≤
      (8001+2*B) * (n : ℝ)^(-a) := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hq hi) hB
    calc
      _ ≤ 8001*(n : ℝ)^(-a)+B*((n : ℝ)^(-a)+(n : ℝ)^(-a)) :=
        add_le_add (mul_le_mul_of_nonneg_left hδ (by norm_num)) hh
      _ = _ := (show ∀ x y : ℝ, 8001*x+y*(x+x)=(8001+2*y)*x by
        intro x y; ring) _ _
  have hrt : (8001*(n : ℝ)^(-c) + B*((n : ℝ)/prefixD n^4000 + 1/prefixD n)) ^
      (1/(8000 : ℝ)) ≤ (8001+2*B)^(1/(8000 : ℝ)) * (n : ℝ)^(-a/8000) := by
    calc
      _ ≤ ((8001+2*B) * (n : ℝ)^(-a))^(1/(8000 : ℝ)) :=
        Real.rpow_le_rpow (add_nonneg
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hn0.le _))
          (mul_nonneg hB (add_nonneg (div_nonneg hn0.le (pow_nonneg hD0.le _))
            (div_nonneg zero_le_one hD0.le)))) hsum (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_mul hn0.le]
        congr 2
        ring
  have hδ' : (n : ℝ)^(-c) ≤ (n : ℝ)^(-a/8000) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have herr : prefixSpectralError n c ≤ L * (n : ℝ)^(-a/8000) := by
    unfold prefixSpectralError
    change 4*(8001*(n : ℝ)^(-c)+B*((n : ℝ)/prefixD n^4000+1/prefixD n))^
      (1/(8000 : ℝ))+7*(n : ℝ)^(-c) ≤ _
    dsimp [L]
    nlinarith
  calc
    _ ≤ (2*L)*(n : ℝ)^(-a/8000) := by linarith
    _ ≤ (n : ℝ)^(a/16000)*(n : ℝ)^(-a/8000) :=
      mul_le_mul_of_nonneg_right hLr (by positivity)
    _ = (n : ℝ)^(-(a/16000)) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring

end SharpTerminalLeave

end

end OAI
