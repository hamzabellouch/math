import OAI.NumberTheory.JointDickman.Counting.CountingRamp
import OAI.NumberTheory.JointDickman.Counting.PeriodicProfileMeans

namespace OAI

/-! # The counting-ramp error occupies a short interval of origins -/
namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem periodic_counting_band_bound {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) {A d δ : ℝ} (hA : 0 ≤ A) (hf : ∀ r, 0 ≤ f r ∧ f r ≤ A)
    (hd : 0 < d) (hδ : 0 < δ) (offset x : ℝ) (K : ℕ) :
    (∑ u ∈ range K, if x-δ < ((u : ℝ)+offset)/d ∧ ((u : ℝ)+offset)/d < x then f u else 0) ≤
      (d*δ+1)*((∑ r, f r)/(q : ℝ))+2*q*A := by
  let S := (range K).filter (fun u : ℕ =>
    x-δ < ((u : ℝ)+offset)/d ∧ ((u : ℝ)+offset)/d < x)
  have heq : (∑ u ∈ range K, if x-δ < ((u : ℝ)+offset)/d ∧ ((u : ℝ)+offset)/d < x then f u else 0) =
      ∑ u ∈ S, f u := by rw [sum_filter]
  rw [heq]
  have hconv : ∀ a ∈ S, ∀ b ∈ S, ∀ n, a ≤ n → n ≤ b → n ∈ S := by
    intro a ha b hb n han hnb
    obtain ⟨_,ha⟩ := mem_filter.mp ha
    obtain ⟨hbK,hb⟩ := mem_filter.mp hb
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (hnb.trans_lt (mem_range.mp hbK)),?_⟩
    have han' : (a : ℝ) ≤ n := by exact_mod_cast han
    have hnb' : (n : ℝ) ≤ b := by exact_mod_cast hnb
    exact ⟨ha.1.trans_le (div_le_div_of_nonneg_right (by linarith) hd.le),
      (div_le_div_of_nonneg_right (by linarith) hd.le).trans_lt hb.2⟩
  obtain ⟨lo,hi,hle,hS⟩ := finite_nat_convex_eq_interval S hconv
  have hcard : ((hi-lo : ℕ) : ℝ) ≤ d*δ+1 := by
    by_cases he : lo = hi
    · subst hi
      simp only [Nat.sub_self,Nat.cast_zero]
      positivity
    · have hlt : lo < hi := lt_of_le_of_ne hle he
      have hlo : lo ∈ S := by rw [hS]; exact mem_Ico.mpr ⟨le_rfl,hlt⟩
      have hhi : hi-1 ∈ S := by rw [hS]; exact mem_Ico.mpr ⟨by omega,by omega⟩
      have hl := (mem_filter.mp hlo).2.1
      have hu := (mem_filter.mp hhi).2.2
      have hl' := (lt_div_iff₀ hd).mp hl
      have hu' := (div_lt_iff₀ hd).mp hu
      have hh : (0 : ℕ) < hi := by omega
      rw [Nat.cast_sub hle,Nat.cast_sub hh, Nat.cast_one] at *
      nlinarith
  rw [hS]
  have hm : 0 ≤ (∑ r, f r)/(q : ℝ) := div_nonneg (sum_nonneg (fun r _ => (hf r).1)) (Nat.cast_nonneg _)
  have he := (le_abs_self _).trans (real_periodic_interval_error f hA
    (fun r => by rw [abs_of_nonneg (hf r).1]; exact (hf r).2) hle)
  have hc := mul_le_mul_of_nonneg_right hcard hm
  linarith

open Classical in
theorem periodic_counting_ramp_error {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) {A d δ : ℝ} (hA : 0 ≤ A) (hf : ∀ r, 0 ≤ f r ∧ f r ≤ A)
    (hd : 0 < d) (hδ : 0 < δ) (offset x : ℝ) (K : ℕ) :
    (∑ u ∈ range K, f u*|(if ((u : ℝ)+offset)/d < x then (1 : ℝ) else 0)-
      countingRamp δ (((u : ℝ)+offset)/d) x|) ≤
      (d*δ+1)*((∑ r, f r)/(q : ℝ))+2*q*A := by
  apply le_trans _ (periodic_counting_band_bound f hA hf hd hδ offset x K)
  apply sum_le_sum
  intro u _
  obtain ⟨hpos,herr⟩ := countingRamp_sharp_error hδ (((u : ℝ)+offset)/d) x
  rw [abs_of_nonneg hpos]
  by_cases h : x-δ < ((u : ℝ)+offset)/d ∧ ((u : ℝ)+offset)/d < x
  · rw [ite_eq_left h]
    have hh : ((u : ℝ)+offset)/d < x ∧ x < ((u : ℝ)+offset)/d+δ := by
      constructor <;> linarith [h.1,h.2]
    rw [ite_eq_left hh] at herr
    exact (mul_le_mul_of_nonneg_left herr (hf u).1).trans_eq (mul_one _)
  · rw [ite_eq_right h]
    have hh : ¬ (((u : ℝ)+offset)/d < x ∧ x < ((u : ℝ)+offset)/d+δ) := by
      intro hh
      exact h ⟨by linarith [hh.2],hh.1⟩
    rw [ite_eq_right hh] at herr
    exact (mul_le_mul_of_nonneg_left herr (hf u).1).trans_eq (mul_zero _)

open Classical in
theorem periodic_counting_ramp_error_eventually {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) {A δ : ℝ} (hA : 0 ≤ A) (hf : ∀ r, 0 ≤ f r ∧ f r ≤ A)
    (hδ : 0 < δ) {T : ℕ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (offset x : ℝ) (K : ℕ),
      (∑ u ∈ range K, f u*|(if ((u : ℝ)+offset)/((T : ℝ)*(N+1)) < x then (1 : ℝ) else 0)-
        countingRamp δ (((u : ℝ)+offset)/((T : ℝ)*(N+1))) x|)/(N : ℝ) <
          (T : ℝ)*δ*((∑ r, f r)/(q : ℝ))+ε := by
  let μ := (∑ r, f r)/(q : ℝ)
  let C := ((T : ℝ)*δ+1)*μ+2*q*A
  have hlim : Tendsto (fun N : ℕ => C/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  filter_upwards [hlim.eventually (Iio_mem_nhds hε),eventually_gt_atTop 0] with N hN hN0
  intro offset x K
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hh := periodic_counting_ramp_error f hA hf
    (show (0 : ℝ) < (T : ℝ)*(N+1) by positivity) hδ offset x K
  calc
    _ ≤ ((((T : ℝ)*(N+1))*δ+1)*μ+2*q*A)/(N : ℝ) :=
      div_le_div_of_nonneg_right hh hNr.le
    _ = (T : ℝ)*δ*μ+C/(N : ℝ) := by dsimp [C]; field_simp; ring
    _ < _ := by linarith

end JointDickman

end OAI
