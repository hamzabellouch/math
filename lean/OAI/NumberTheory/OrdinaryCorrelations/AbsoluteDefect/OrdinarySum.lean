import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set

namespace OrdinaryTriangular

def ordinarySum (a : ℕ → ℂ) (N : ℕ) : ℂ := ∑n∈Finset.Icc 1 N,a n

def triangle (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑n∈Finset.Icc 1 N,((N:ℂ)-(n:ℂ))*a n

lemma triangle_difference (a : ℕ → ℂ) (N H : ℕ) :
    triangle a (N+H)-triangle a N-(H:ℂ)*ordinarySum a N =
      ∑n∈Finset.Icc (N+1) (N+H),(((N+H:ℕ):ℂ)-(n:ℂ))*a n := by
  have hu : Finset.Icc 1 (N+H)=Finset.Icc 1 N∪Finset.Icc (N+1) (N+H) := by
    ext n
    simp only [Finset.mem_Icc,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Icc 1 N) (Finset.Icc (N+1) (N+H)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have := Finset.mem_Icc.mp hn
    have := Finset.mem_Icc.mp hn'
    omega
  unfold triangle ordinarySum
  rw [hu,Finset.sum_union hd,Finset.mul_sum]
  have he : (∑n∈Finset.Icc 1 N,(((N+H:ℕ):ℂ)-(n:ℂ))*a n) =
      (∑n∈Finset.Icc 1 N,((N:ℂ)-(n:ℂ))*a n)+(∑n∈Finset.Icc 1 N,(H:ℂ)*a n) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  rw [he]
  ring

lemma unsigned_tail_bound (a : ℕ → ℂ) (ha : ∀n, ‖a n‖≤1) (N H : ℕ) :
    ‖∑n∈Finset.Icc (N+1) (N+H),(((N+H:ℕ):ℂ)-(n:ℂ))*a n‖≤(H:ℝ)^2 := by
  have hpt (n : ℕ) (hn : n∈Finset.Icc (N+1) (N+H)) :
      ‖(((N+H:ℕ):ℂ)-(n:ℂ))*a n‖≤(H:ℝ) := by
    have hnle : (n:ℝ)≤(N:ℝ)+(H:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hnge : (N:ℝ)≤(n:ℝ) := by exact_mod_cast (show N≤n by have := (Finset.mem_Icc.mp hn).1; omega)
    have he : (((N+H:ℕ):ℂ)-(n:ℂ))=((N:ℝ)+(H:ℝ)-(n:ℝ):ℝ) := by push_cast; rfl
    rw [norm_mul,he,Complex.norm_real,Real.norm_of_nonneg (by linarith)]
    have hh := mul_le_mul_of_nonneg_left (ha n) (show 0≤(N:ℝ)+(H:ℝ)-(n:ℝ) by linarith)
    nlinarith
  calc
    _ ≤ ∑n∈Finset.Icc (N+1) (N+H),‖(((N+H:ℕ):ℂ)-(n:ℂ))*a n‖ := norm_sum_le _ _
    _ ≤ ∑n∈Finset.Icc (N+1) (N+H),(H:ℝ) := Finset.sum_le_sum hpt
    _ = _ := by simp [Nat.card_Icc]; ring

theorem unsmoothing (a : ℕ → ℂ) (ha : ∀n, ‖a n‖≤1) (N H : ℕ) :
    (H:ℝ)*‖ordinarySum a N‖ ≤ ‖triangle a (N+H)‖+‖triangle a N‖+(H:ℝ)^2 := by
  have he := triangle_difference a N H
  have hrepr : (H:ℂ)*ordinarySum a N=triangle a (N+H)-triangle a N-
      (∑n∈Finset.Icc (N+1) (N+H),(((N+H:ℕ):ℂ)-(n:ℂ))*a n) := by
    linear_combination -he
  calc
    (H:ℝ)*‖ordinarySum a N‖ = ‖(H:ℂ)*ordinarySum a N‖ := by simp
    _ = _ := congrArg norm hrepr
    _ ≤ ‖triangle a (N+H)-triangle a N‖+
      ‖∑n∈Finset.Icc (N+1) (N+H),(((N+H:ℕ):ℂ)-(n:ℂ))*a n‖ := norm_sub_le _ _
    _ ≤ (‖triangle a (N+H)‖+‖triangle a N‖)+(H:ℝ)^2 :=
      add_le_add (norm_sub_le _ _) (unsigned_tail_bound a ha N H)

end OrdinaryTriangular

end

end OAI
