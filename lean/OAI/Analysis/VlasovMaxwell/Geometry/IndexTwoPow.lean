import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.CappedRepresentativePos

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma index_lt_of_two_pow_le {n N : ℕ} {B : ℝ}
    (hn : (2:ℝ)^n ≤ B) (hN : B < (2:ℝ)^N) : n<N := by
  by_contra hc
  have he := pow_le_pow_right₀ (show (1:ℝ)≤2 by norm_num) (Nat.le_of_not_gt hc)
  exact (not_lt_of_ge (he.trans hn)) hN

lemma cappedRepresentative_mul_pow (n : ℕ) : cappedRepresentative n*(2:ℝ)^n=1 := by
  simp [cappedRepresentative,inv_pow]

lemma direction_far_indices {P T : ℝ} {N : ℕ} {k : Fin 4→ℕ}
    (hP : 0 < P) (hp : sourceRepresentative (k 0) ≤ 128*P)
    (hθφ : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2))
    (hfar : 1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3)))
    (hN₀ : 2*P < (2:ℝ)^N)
    (hN₁ : 4096*P*Real.sqrt (max 1 T) < (2:ℝ)^N)
    (hN₃ : (4096*P)^2*max 1 T < (2:ℝ)^N) : ∀i,k i<N := by
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let H := max 1 T
  let r := H*cappedRepresentative (k 3)
  have hθ : 0 ≤ θ := (cappedRepresentative_pos _).le
  have hθ1 : θ ≤ 1 := cappedRepresentative_le_one _
  have hH : 0 ≤ H := (show (0:ℝ)≤1 by norm_num).trans (le_max_left _ _)
  have hr : 0 ≤ r := mul_nonneg hH (cappedRepresentative_pos _).le
  have hrH : r ≤ H := mul_le_of_le_one_right hH (cappedRepresentative_le_one _)
  have hsqrt : Real.sqrt r ≤ Real.sqrt H := Real.sqrt_le_sqrt hrH
  have hfp : 1/32 ≤ 128*P*θ*Real.sqrt r := hfar.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hθ) (Real.sqrt_nonneg _))
  have hfθ : 1/32 ≤ 128*P*θ*Real.sqrt H := hfp.trans
    (mul_le_mul_of_nonneg_left hsqrt (by positivity))
  have hfφ : 1/32 ≤ 128*P*φ*Real.sqrt H := hfθ.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθφ (by positivity)) (Real.sqrt_nonneg _))
  have hrfirst : 1/32 ≤ 128*P*Real.sqrt r := hfp.trans
    (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) hθ1) (Real.sqrt_nonneg _))
  have hrbound : 1 ≤ (4096*P)^2*r := by
    have hsq := mul_self_le_mul_self (show (0:ℝ)≤1/32 by norm_num) hrfirst
    have hsq' : (1/32:ℝ)^2 ≤ (128*P*Real.sqrt r)^2 := by simpa only [pow_two] using hsq
    rw [mul_pow,Real.sq_sqrt hr] at hsq'
    nlinarith only [hsq']
  have hn0 : (2:ℝ)^(k 0) ≤ 2*P := by
    dsimp [sourceRepresentative] at hp
    linarith only [hp]
  have hn1 : (2:ℝ)^(k 1) ≤ 4096*P*Real.sqrt H := by
    have hh := mul_le_mul_of_nonneg_right hfθ (show (0:ℝ)≤2^(k 1) by positivity)
    have he : θ*(2:ℝ)^(k 1)=1 := cappedRepresentative_mul_pow _
    have hprod : 128*P*θ*Real.sqrt H*(2:ℝ)^(k 1)=128*P*Real.sqrt H := by
      calc
        _ = 128*P*Real.sqrt H*(θ*(2:ℝ)^(k 1)) := by ring
        _ = _ := by rw [he,mul_one]
    rw [hprod] at hh
    linarith only [hh]
  have hn2 : (2:ℝ)^(k 2) ≤ 4096*P*Real.sqrt H := by
    have hh := mul_le_mul_of_nonneg_right hfφ (show (0:ℝ)≤2^(k 2) by positivity)
    have he : φ*(2:ℝ)^(k 2)=1 := cappedRepresentative_mul_pow _
    have hprod : 128*P*φ*Real.sqrt H*(2:ℝ)^(k 2)=128*P*Real.sqrt H := by
      calc
        _ = 128*P*Real.sqrt H*(φ*(2:ℝ)^(k 2)) := by ring
        _ = _ := by rw [he,mul_one]
    rw [hprod] at hh
    linarith only [hh]
  have hn3 : (2:ℝ)^(k 3) ≤ (4096*P)^2*H := by
    have hh := mul_le_mul_of_nonneg_right hrbound (show (0:ℝ)≤2^(k 3) by positivity)
    have he : r*(2:ℝ)^(k 3)=H := by
      dsimp [r]
      rw [mul_assoc,cappedRepresentative_mul_pow,mul_one]
    rw [one_mul,mul_assoc,he] at hh
    exact hh
  intro i
  fin_cases i
  · exact index_lt_of_two_pow_le hn0 hN₀
  · exact index_lt_of_two_pow_le hn1 hN₁
  · exact index_lt_of_two_pow_le hn2 hN₁
  · exact index_lt_of_two_pow_le hn3 hN₃

end RVM

open Set

namespace RVM

lemma exists_dyadic_count_log {B : ℝ} (hB : 1 ≤ B) :
    ∃N : ℕ, B < (2:ℝ)^N ∧ (N:ℝ) ≤ 2+Real.log B/Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : 0 ≤ Real.log B/Real.log 2 := div_nonneg (Real.log_nonneg hB) h2.le
  let n := ⌈Real.log B/Real.log 2⌉₊
  refine ⟨n+1,?_,?_⟩
  · apply (Real.log_lt_log_iff (zero_lt_one.trans_le hB) (by positivity)).mp
    rw [Real.log_pow,Nat.cast_add,Nat.cast_one]
    have hc : Real.log B/Real.log 2 < (n:ℝ)+1 := by
      have hh := Nat.le_ceil (Real.log B/Real.log 2)
      dsimp [n]
      linarith only [hh]
    exact (div_lt_iff₀ h2).mp hc
  · have hh : (n:ℝ) < Real.log B/Real.log 2+1 := Nat.ceil_lt_add_one h0
    push_cast
    linarith only [hh]

lemma exists_far_dyadic_count (T : ℝ) :
    ∃C : ℝ, 0 ≤ C ∧ ∀P : ℝ, 0 < P → 1 ≤ Real.log (2+P) →
      ∃N : ℕ, 2*P < (2:ℝ)^N ∧
        4096*P*Real.sqrt (max 1 T) < (2:ℝ)^N ∧
        (4096*P)^2*max 1 T < (2:ℝ)^N ∧
        (N:ℝ) ≤ C*Real.log (2+P) := by
  let H := max 1 T
  let D := 16777216*H
  let C := 2+Real.log D/Real.log 2+2/Real.log 2
  have hH1 : 1 ≤ H := le_max_left _ _
  have hH : 0 < H := zero_lt_one.trans_le hH1
  have hD1 : 1 ≤ D := by dsimp [D]; linarith only [hH1]
  have hD : 0 < D := zero_lt_one.trans_le hD1
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro P hP hL
  let B := D*(2+P)^2
  have hB1 : 1 ≤ B := by
    have hs : 1 ≤ (2+P)^2 := by nlinarith only [hP,sq_nonneg P]
    simpa only [one_mul] using (mul_le_mul hD1 hs (by norm_num) hD.le : (1:ℝ)*1 ≤ D*(2+P)^2)
  obtain ⟨N,hN,hNc⟩ := exists_dyadic_count_log hB1
  refine ⟨N,?_,?_,?_,?_⟩
  · have hh : 2*P < D*(2+P)^2 := by
      have hd : (2:ℝ) ≤ D := by dsimp [D]; linarith only [hH1]
      have hx : 2*(2+P)^2 ≤ D*(2+P)^2 := mul_le_mul_of_nonneg_right hd (sq_nonneg _)
      nlinarith only [hx,hP,sq_nonneg P]
    exact hh.trans hN
  · have hsH : 1 ≤ Real.sqrt H := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hH1
    have hsqH : (Real.sqrt H)^2=H := Real.sq_sqrt hH.le
    have hterm : 4096*P*Real.sqrt H < D*(2+P)^2 := by
      have hx : 0 ≤ P*(Real.sqrt H)*(Real.sqrt H-1) := mul_nonneg (mul_nonneg hP.le (Real.sqrt_nonneg _)) (sub_nonneg.mpr hsH)
      have hy : 0 ≤ H*P^2 := mul_nonneg hH.le (sq_nonneg _)
      dsimp [D]
      nlinarith only [hx,hy,hsqH,hH1,hP,mul_pos hP hH]
    exact hterm.trans hN
  · have hterm : (4096*P)^2*H < D*(2+P)^2 := by
      have hh : P^2 < (2+P)^2 := by nlinarith only [hP]
      have hm := mul_lt_mul_of_pos_left hh (show 0 < 16777216*H by positivity)
      dsimp [D]
      nlinarith only [hm]
    exact hterm.trans hN
  · have hlog : Real.log B=Real.log D+2*Real.log (2+P) := by
      dsimp [B]
      rw [Real.log_mul (ne_of_gt hD) (ne_of_gt (sq_pos_of_pos (by linarith only [hP]))),Real.log_pow]
      norm_num
    rw [hlog] at hNc
    apply hNc.trans
    have hcoeff : 0 ≤ 2+Real.log D/Real.log 2 := by positivity
    have hh := mul_le_mul_of_nonneg_left hL hcoeff
    dsimp [C]
    calc
      _ = (2+Real.log D/Real.log 2)+(2/Real.log 2)*Real.log (2+P) := by ring
      _ ≤ (2+Real.log D/Real.log 2)*Real.log (2+P)+(2/Real.log 2)*Real.log (2+P) := by linarith only [hh]
      _ = _ := by ring

end RVM

end

end OAI
