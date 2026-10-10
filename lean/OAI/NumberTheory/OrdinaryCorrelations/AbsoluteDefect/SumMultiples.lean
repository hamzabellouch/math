import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.WeightedPartialSumBound
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TentPhaseIntegral

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset

namespace OrdinaryLogIntegral
open Finset

lemma sum_multiples (f : ℕ → ℂ) (A d : ℕ) (hd : 0 < d) :
    (∑ n ∈ range (A+1), if d ∣ n then f n else 0) =
      ∑ k ∈ range (A/d+1), f (d*k) := by
  rw [← sum_filter]
  symm
  apply sum_bij (fun k _ => d*k)
  · intro k hk
    apply mem_filter.mpr
    constructor
    · apply mem_range.mpr
      have hh : k ≤ A/d := by have := mem_range.mp hk; omega
      have := (Nat.le_div_iff_mul_le hd).mp hh
      nlinarith
    · exact dvd_mul_right d k
  · intro k hk m hm hkm
    exact Nat.eq_of_mul_eq_mul_left hd hkm
  · intro n hn
    obtain ⟨hnA, hdN⟩ := mem_filter.mp hn
    refine ⟨n/d, ?_, Nat.mul_div_cancel' hdN⟩
    apply mem_range.mpr
    have hna : n ≤ A := by have := mem_range.mp hnA; omega
    have := Nat.div_le_div_right (c := d) hna
    omega
  · intro k hk
    rfl

lemma sum_range_drop_zero (f : ℕ → ℂ) (N b : ℕ) (hb : b ≤ N)
    (hz : ∀ n < b, f n = 0) :
    (∑ n ∈ range N, f n) = ∑ n ∈ range (N-b), f (b+n) := by
  have he : N = b+(N-b) := by omega
  conv_lhs => rw [he, sum_range_add]
  have hh : (∑ n ∈ range b, f n) = 0 := sum_eq_zero (fun n hn => hz n (mem_range.mp hn))
  rw [hh, zero_add]

noncomputable def divisorTriangle (t : ℝ) (B d : ℕ) : ℂ :=
  ∑ n ∈ range (6*B+1), if d ∣ n then tentPhase t B (2*B) n else 0

lemma divisorTriangle_eq (t : ℝ) (B d : ℕ) (hd : 0 < d) :
    divisorTriangle t B d =
      ∑ k ∈ range (6*B/d+1), tentPhase t B (2*B) ((d : ℝ)*k) := by
  unfold divisorTriangle
  rw [sum_multiples _ _ _ hd]
  simp only [Nat.cast_mul]

lemma divisorTriangle_low_error (t : ℝ) (B d : ℕ) (hB : 0 < B) (hd : 0 < d) :
    ‖divisorTriangle t B d - (((d : ℝ)*(2*B))⁻¹ : ℝ) • triangleMellin t B (2*B)‖ ≤
      ((6*B/d+1 : ℕ) : ℝ)*d*((2*(B : ℝ))⁻¹+|t|/B) := by
  rw [divisorTriangle_eq t B d hd]
  apply tent_progression_error t B (2*B) d (6*B/d+1) (by exact_mod_cast hB) (by positivity)
    (by exact_mod_cast hd)
  have hh := Nat.lt_mul_div_succ (6*B) hd
  have hh' : (6*B : ℝ) < (d : ℝ)*(6*B/d+1 : ℕ) := by exact_mod_cast hh
  linarith

lemma divisorTriangle_shift (t : ℝ) (B d : ℕ) (hB : 0 < B) (hd : 0 < d) :
    divisorTriangle t B d =
      ∑ k ∈ range ((6*B/d+1)-B/d), tentPhase t B (2*B) ((d : ℝ)*((B/d : ℕ)+k)) := by
  rw [divisorTriangle_eq t B d hd]
  have hb : B/d ≤ 6*B/d+1 := by
    have := Nat.div_le_div_right (c := d) (show B ≤ 6*B by omega)
    omega
  rw [sum_range_drop_zero _ _ _ hb]
  · simp only [Nat.cast_add]
  · intro n hn
    apply tentPhase_zero_left _ _ _ _ (by positivity)
    have hh : d*n ≤ B := by
      have hnn : n ≤ B/d := by omega
      have := (Nat.le_div_iff_mul_le hd).mp hnn
      nlinarith
    exact_mod_cast hh

theorem divisorTriangle_high (t : ℝ) (B d K : ℕ) (hB : 0 < B) (hd : 0 < d)
    (hdB : d ≤ B) (ht : t ≠ 0) (hK : 0 < K) :
    ‖divisorTriangle t B d‖ ≤
      (1+((6*B/d+1-B/d : ℕ) : ℝ)*d/(2*B)) *
        (Real.sqrt (differencingBudget t (B/d : ℕ) (6*B/d+1-B/d) K)/(K : ℝ)) := by
  rw [divisorTriangle_shift t B d hB hd]
  exact weighted_discrete_logphase t B (2*B) d (B/d : ℕ) (6*B/d+1-B/d) K
    (by positivity) (by exact_mod_cast hd)
    (by exact_mod_cast Nat.div_pos hdB hd) ht hK

end OrdinaryLogIntegral

end

end OAI
