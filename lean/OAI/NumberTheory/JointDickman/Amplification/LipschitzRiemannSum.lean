import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-! # A finite Riemann-sum error for a Lipschitz function -/
namespace JointDickman
open Finset MeasureTheory

lemma lipschitz_riemann_sum_error (f : ℝ → ℂ) (M : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ Set.Icc (0:ℝ) M, ∀ y ∈ Set.Icc (0:ℝ) M,
      ‖f y-f x‖ ≤ L*|y-x|) :
    ‖(∑ n ∈ range M, f (n+1)) - ∫ x in (0:ℝ)..M, f x‖ ≤ M*L := by
  have hcont : ContinuousOn f (Set.Icc (0:ℝ) M) :=
    (LipschitzOnWith.of_dist_le' (fun x hx y hy => by
      simpa only [dist_eq_norm, Real.norm_eq_abs] using hf y hy x hx)).continuousOn
  have hint (n : ℕ) (hn : n < M) : IntervalIntegrable f volume n (n+1) := by
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (n:ℝ) ≤ n+1)] at hx
    exact ⟨(Nat.cast_nonneg n).trans hx.1, hx.2.trans (by exact_mod_cast hn)⟩
  have herror (n : ℕ) (hn : n < M) :
      ‖f (n+1) - ∫ x in (n:ℝ)..n+1, f x‖ ≤ L := by
    have he : f (n+1) - (∫ x in (n:ℝ)..n+1, f x) =
        ∫ x in (n:ℝ)..n+1, (f (n+1)-f x) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const) (hint n hn),
        intervalIntegral.integral_const]
      simp
    rw [he]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := L)
      (a := (n:ℝ)) (b := n+1) (f := fun x => f (n+1)-f x) (by
        intro x hx
        rw [Set.uIoc_of_le (by norm_num : (n:ℝ) ≤ n+1)] at hx
        have hxM : x ∈ Set.Icc (0:ℝ) M :=
          ⟨(Nat.cast_nonneg n).trans hx.1.le, hx.2.trans (by exact_mod_cast hn)⟩
        have hnM : (n:ℝ)+1 ∈ Set.Icc (0:ℝ) M :=
          ⟨by positivity, by exact_mod_cast hn⟩
        apply (hf x hxM (n+1) hnM).trans
        apply mul_le_of_le_one_right hL
        rw [abs_of_nonneg (sub_nonneg.mpr hx.2)]
        linarith [hx.1])
    simpa only [add_sub_cancel_left, abs_one, mul_one] using hh
  have hs : (∑ n ∈ range M, ∫ x in (n:ℝ)..n+1, f x) = ∫ x in (0:ℝ)..M, f x := by
    convert intervalIntegral.sum_integral_adjacent_intervals
      (a := fun n : ℕ => (n:ℝ)) (fun n hn => by simpa only [Nat.cast_add, Nat.cast_one] using hint n hn) using 1 <;> simp
  rw [← hs, ← sum_sub_distrib]
  exact (norm_sum_le _ _).trans ((sum_le_sum (fun n hn => herror n (mem_range.mp hn))).trans_eq (by simp))

lemma riemann_sum_range_succ_eq_Icc {E : Type*} [AddCommMonoid E] (f : ℕ → E) (M : ℕ) :
    (∑ n ∈ range M, f (n+1)) = ∑ n ∈ Icc 1 M, f n := by
  apply sum_bij (fun n _ => n+1)
  · intro n hn
    exact mem_Icc.mpr ⟨by omega, by have := mem_range.mp hn; omega⟩
  · intro n hn m hm he
    omega
  · intro n hn
    refine ⟨n-1, mem_range.mpr ?_, ?_⟩
    · have := mem_Icc.mp hn
      omega
    · have := mem_Icc.mp hn
      omega
  · intro n hn
    rfl

end JointDickman

end OAI
